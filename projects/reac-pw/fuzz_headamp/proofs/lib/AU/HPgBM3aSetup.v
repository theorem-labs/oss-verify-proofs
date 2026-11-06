(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b (hd_getr_z,
   hd_aview_some, hd_aview_grows, restated as su_getr_z, su_aview_some, su_aview_grows) and
   proofs/reac-pw/fuzz_role/lib/A/RPgScanSetup.v at a1fdf6ce036 (su_soff; the set-up's shape: one engine run over the
   first block's three fields decided by one shadow entry, split on the booleans) for reac-pw/fuzz_headamp image A;
   the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3aSetupBlk.v, with its module paths, module names, addresses and numbers changed; 1543 of its 1685 lines of code are new or changed and 606 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; the addresses are measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections
   are byte-equal to the pin's except .note.gnu.build-id): the SET-UP piece of the checking segment M03 of LLVMFuzzerTestOneInput,
   from the cut X 0x82fdc to the pair loop's head PAIR 0x8314c, to RC 0x83850 or to RCM 0x8385c -
   lib/AU/HPgSegM.v's hqu_piece_M3a_setup_stmt.

   THE CODE (s1 = R the real frame, s3 = shadow_addr F, s5 = F, s7 = 1 - the null flag, s11 = SHADOW_OFF):
   - 0x82fdc  addi s2,s5,704          s2 := x = F + 0x2c0
   - 0x82fe0 .. 0x83020               x's seventeen shadow granules 88 .. 104 := 0 (HPgSteps.hdu_scope_x_in)
   - 0x83024 .. 0x83030               a2 := 136, a0 := x, a1 := 0, jal __asan_memset, ra 0x83034
   - 0x83034  li a3,-1; 0x83038 beqz s7 -> RCM 0x8385c (the null flag is 1)
   - 0x8303c .. 0x83054               pp->is_props through its instrumented check; beqz -> RCM
   - 0x83058  sd s2,312(s1)           R+0x138 := x
   - 0x8305c .. 0x83074               pp->params_struct through its instrumented check; beqz -> RC 0x83850
   - 0x83078 .. 0x83148               the loop's constants, the entry table's four addresses and the three
                                      `fmv.w.x` (fs1 = -1.0f, fs2 = 256.0f, fs3 = 2^63 as binary32)
   - 0x8314c                          the pair loop's head. The cut hqu_cut_PAIR carries 0 < hqu_nent r and
     image B's set-up does not test n_ent, so when the record has no entry this file walks on through the
     pair head's five instructions (the n_ent read through its instrumented check and `bge a2,a3`) to RC.
   Every instrumented check reads a shadow byte of the first block, whose shadow is 0, so no slow path and
   no error path is reached. Proves function LLVMFuzzerTestOneInput (this piece of its walk).

   WHAT IT ASSUMES. Two Section hypotheses: AMEMSET, the kernel's contract of __asan_memset at image B's
   entry 0x52228 at any float state (YG0d's AsanAPI field aa_asan_memset), and MTL, the meter's laws. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgMem HPgSteps HPgIntrinU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgSeg HPgSegM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the frame object x of image B: 136 bytes at F + 0x2c0, granules 88 .. 104 *)
Definition SU_XO : Z := 0x2c0.

(* ================================ generic helpers ================================ *)
Lemma su_soff : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* a register named by Z_to_bv 5 n is the register named by the numeral n *)
Lemma su_getr_z : forall (regs : bvmap 5 word) (r : bv 5) n, bv_unsigned r = n ->
getr regs (Z_to_bv 5 n) = getr regs r.
Proof.
intros regs r n H. f_equal. apply bv_eq. subst n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (u5_range r). change (bv_modulus 5) with 32. lia.
Qed.

(* a cell of a region, read back after a run *)
Lemma su_cell : forall E m b cs off e v, Forall (YP09.chunk_ok rsegs E m b) cs ->
In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem rsegs m (b + off) 8 v.
Proof.
intros E m b cs off e v H Hin He Hv.
exact (val_of_chunk_ok rsegs E m b off 8 e v (proj1 (Forall_forall _ _) H _ Hin) He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)).
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a byte a block or a frame holds is present, so it reads as something *)
Lemma su_aview_some : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* every byte that read as something still does after a step that keeps every present byte present *)
Lemma su_notmod : forall y, 0 <= y < 2 ^ 64 -> (-1 - y) mod 2 ^ 64 = 2 ^ 64 - 1 - y.
Proof.
intros y Hy. rewrite <- (Z.mod_add (-1 - y) 1 (2 ^ 64)) by lia.
replace (-1 - y + 1 * 2 ^ 64) with (2 ^ 64 - 1 - y) by ring. apply Z.mod_small. lia.
Qed.
Lemma su_land7 : forall y, 0 <= y -> Z.land y 7 = y mod 8.
Proof. intros y Hy. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma su_aview_grows_m : forall (H : word -> bool) (m m' : word -> option byte),
mem_grows (mrestrict H m) (mrestrict H m') ->
forall a, aview rsegs H m a <> None -> aview rsegs H m' a <> None.
Proof.
intros H m m' Hg a Hv. unfold aview, mbyte in *.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em.
- specialize (Hg (Z_to_bv 64 a) ltac:(rewrite Em; discriminate)).
  destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exfalso; exact (Hg eq_refl)].
- destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.
Lemma su_aview_grows : forall (H : word -> bool) (m m' : word -> option byte),
(forall x, apresent H m x -> apresent H m' x) ->
forall a, aview rsegs H m a <> None -> aview rsegs H m' a <> None.
Proof.
intros H m m' Hg a Hv. unfold aview, mbyte, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exact Hv|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Hm.
- assert (Hp : apresent H m a) by (split; [exact Hh | exists b; exact Hm]).
  destruct (Hg a Hp) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.
(* a byte reads the same at an address and at its 64-bit residue *)
Lemma su_aview_wrap : forall (H : word -> bool) (m : word -> option byte) x,
aview rsegs H m x = aview rsegs H m (x mod 2 ^ 64).
Proof.
intros H m x. unfold aview, mbyte, mrestrict. rewrite HPgSteps.Z_to_bv_mod64. reflexivity.
Qed.
(* a 4-byte value whose bytes all still read as something reads as some value *)
Lemma su_rd32_grows : forall (H H' : word -> bool) (m m' : word -> option byte) a ev,
rd32 (aview rsegs H m) a ev ->
(forall x, aview rsegs H m x <> None -> aview rsegs H' m' x <> None) ->
exists ev', rd32 (aview rsegs H' m') a ev'.
Proof.
intros H H' m m' a ev Hr Hg.
assert (Hk : forall k, (k < 4)%nat -> exists b, aview rsegs H' m' (a + Z.of_nat k) = Some b /\ 0 <= b < 256).
{ intros k Hk. specialize (Hr k Hk).
  destruct (aview rsegs H' m' (a + Z.of_nat k)) as [b|] eqn:E.
  - exists b. split; [reflexivity|].
    unfold aview in E. destruct (mbyte rsegs (mrestrict H' m') (a + Z.of_nat k)) as [bb|] eqn:Eb;
    [|discriminate E]. cbn [option_map] in E. injection E as <-. apply hm_byte_range.
  - exfalso. apply (Hg (a + Z.of_nat k)); [rewrite Hr; discriminate | exact E]. }
destruct (Hk 0%nat ltac:(lia)) as (b0 & E0 & R0). destruct (Hk 1%nat ltac:(lia)) as (b1 & E1 & R1).
destruct (Hk 2%nat ltac:(lia)) as (b2 & E2 & R2). destruct (Hk 3%nat ltac:(lia)) as (b3 & E3 & R3).
exists (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))).
intros k Hk4. unfold le_byte. change (8 * Z.of_nat 4) with 32.
rewrite (Z.mod_small _ (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- rewrite E0. f_equal. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. lia.
- rewrite E1. f_equal. change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256. lia.
- rewrite E2. f_equal. change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536. lia.
- rewrite E3. f_equal. change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 24) with 16777216. lia.
Qed.
End g.

(* the frame for locals is the same object under any layout the journal allows *)
Lemma su_frame_addr_le : forall n ly ly1 ly2 cid pos,
layout_le n ly ly1 -> layout_le n ly ly2 -> frame_addr ly1 cid pos = frame_addr ly2 cid pos.
Proof.
intros n ly ly1 ly2 cid pos (_ & _ & _ & _ & _ & E1 & _) (_ & _ & _ & _ & _ & E2 & _).
unfold frame_addr. rewrite E1, E2. reflexivity.
Qed.

(* ======================= the code tables ======================= *)
Definition su_tblA : ctable := build_table rsegs 0x82fdc 1 TEmpty.
Definition su_tblA_ok : table_ok rsegs su_tblA := build_table_ok0 rsegs 1 0x82fdc ltac:(lia).
Definition su_tblC : ctable := build_table rsegs 0x83024 4 TEmpty.
Definition su_tblC_ok : table_ok rsegs su_tblC := build_table_ok0 rsegs 4 0x83024 ltac:(lia).

(* the symbolic value of a register of the engine's state, as a closed term *)
Ltac su_sv :=
lazymatch goal with |- context [sr_get (ss_regs ?ss) ?r] =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

(* ============ block B: 0x83034 .. RCM 0x8385c / RC 0x83850 / PAIR 0x8314c ============ *)
Definition su_tblB : ctable := build_table rsegs 0x83034 70 TEmpty.
Definition su_tblB_ok : table_ok rsegs su_tblB := build_table_ok0 rsegs 70 0x83034 ltac:(lia).
Definition su_Bx : sv := SOff 27 0.
Definition su_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition su_SH : list shent := [mkSHE 32 0 0x4d20; mkSHE 9 0x140 0x98].
Definition su_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x8 0x150 0x98 0x140
  [ YP09.mkChunk 0x8 (CVal 8 (SOff 32 0x4008));
    YP09.mkChunk 0xe0 (CVal 8 (SAlu ALU_SRL (SOff 32 0x4d14) (SLit 3)));
    YP09.mkChunk 0x108 (CVal 8 (SLit (-16381)));
    YP09.mkChunk 0x120 (CVal 8 (SOff 32 0x4d14));
    YP09.mkChunk 0x148 (CVal 8 (SOff 32 0)) ].
Definition su_rP (cs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x4008 0x4d18 0 0 cs.
Definition su_facts : list (nat * afact) :=
  [(27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 (2 ^ 47 - 0x4d20) 0)].
Definition su_ssB (nz : Z) (cs : list YP09.chunk) : sstate :=
  mkSS 0x83034 (sr_set sr_atoms (Z_to_bv 5 23) (SLit nz)) [su_rR; su_rP cs] None
    (mkFacts su_facts [] []).

(* the three float registers the set-up writes with `fmv.w.x`: fs1, fs2 and fs3 *)
Definition su_fset (f : YK11.FPState) (kk v : Z) : YK11.FPState :=
  YK11.mkFP (bvmap_set (Z_to_bv 5 kk) (nan_box (Z_to_bv 32 v)) (@fp_regs f)) (@fp_csr f).
Definition su_fx3 (f : YK11.FPState) : YK11.FPState :=
  su_fset (su_fset (su_fset f 9 0xbf800000) 18 0x43800000) 19 0x5f000000.

Section fm. Context {rc : YM05.RunCeil}.
(* one `fmv.w.x rd,rs`: the float state gains the nan-boxed low word of rs, nothing else moves *)
Lemma su_fmv : forall (fxA : YK11.FPState) (W : world rsegs) E ss regs mem md
  (Q : world rsegs -> config -> Prop) pc w (kk rs : Z) v (rdb rsb : bv 5),
@st_ok rsegs fxA E ss (restrict (w_H W) (@mkst fxA regs (Z_to_bv 64 pc) mem (seg_rom rsegs))) ->
ss_resv ss = None ->
fetch_word rsegs (Z_to_bv 64 pc) = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_F_X FMT_S rdb rsb, 4) -> rdb = Z_to_bv 5 kk -> rsb = Z_to_bv 5 rs ->
v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4) ->
low32 (getr regs (Z_to_bv 5 rs)) = Z_to_bv 32 v ->
(forall X, @st_ok rsegs (su_fset fxA kk v) E (mkSS (pc + 4) (ss_regs ss) (ss_mem ss) None (ss_facts ss))
   (restrict (w_H W) (@mkst (su_fset fxA kk v) regs (Z_to_bv 64 (pc + 4)) mem (seg_rom rsegs))) ->
 SRr rsegs W (mkCfg (@mkst (su_fset fxA kk v) regs (Z_to_bv 64 (pc + 4)) mem (seg_rom rsegs))
   (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fxA regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) Q.
Proof.
intros fxA W E ss regs mem md Q pc w kk rs v rdb rsb HS Hrv Hf He Hd Hrd Hrs Hpc Hv K. subst rdb rsb.
set (fxB := su_fset fxA kk v).
set (ss' := mkSS (pc + 4) (ss_regs ss) (ss_mem ss) None (ss_facts ss)).
assert (HS' : @st_ok rsegs fxB E ss'
  (restrict (w_H W) (@mkst fxB regs (Z_to_bv 64 (pc + 4)) mem (seg_rom rsegs)))).
{ unfold st_ok in HS |- *.
  destruct HS as (_ & _ & H3 & H4 & _ & H6 & H7 & H8 & H9).
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst] in *.
  subst ss'. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot] in *.
  do 5 (split; [reflexivity|]). split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9]. }
refine (@SRr_msteps_st rsegs fxB img_wx W E ss' (@mkst fxA regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) _ md Q _ HS' _).
- rewrite !restrict_mkst_fx. apply msteps_one; [reflexivity|].
  rewrite (YK0o.fp_step_fmv_w_x fxA rsegs regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (seg_rom rsegs) w
    (Z_to_bv 5 kk) (Z_to_bv 5 rs) Hf He Hd).
  rewrite Hpc, Hv. reflexivity.
- intros ms' mat' HS2 Hlo Hhi Hreg.
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms' HS2 eq_refl) as Ems.
  assert (Hm : ms_mem ms' = mem).
  { apply functional_extensionality. intros x. destruct (w_H W x) eqn:Hx.
    - rewrite (Hhi x Hx). reflexivity.
    - rewrite (Hlo x Hx). cbn [ms_mem restrict mkst]. unfold mrestrict. rewrite Hx. reflexivity. }
  assert (Hr : ms_regs ms' = regs) by (rewrite Hreg; reflexivity).
  rewrite Hm, Hr in Ems. subst ss'. cbn [ss_pc] in Ems. subst ms'.
  apply K. exact HS2.
Qed.
End fm.

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMSET : forall fx' : YK11.FPState, @aintrin_realizes fx' rc rsegs B OSet B_ASAN_MEMSET.

(* ============ block A: X 0x82fdc .. the return of memset(x, 0, 136) 0x83034 ============
   s2 := F + 0x2c0; x's seventeen shadow granules 88 .. 104 := 0 (hdu_scope_x_in); the call
   __asan_memset(x, 0, 136) at B_ASAN_MEMSET with ra 0x83034. *)
Definition su_A_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (R F : Z)
(ly1 : alayout) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte)
(md1 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k /\
frames S1 = frames Sc /\ Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) /\
same_io mdc md1 /\ mo_le MT Sc S1 0 /\ layout_le (length (st_secs S)) ly ly1 /\
(forall r : Z, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
 getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
getr regs1 (Z_to_bv 5 18) = w64 (F + SU_XO) /\
(forall i, 0 <= i < 136 -> aview rsegs (w_H W1) mem1 (F + SU_XO + i) = Some 0) /\
(forall i, 88 <= i < 105 -> aview rsegs (w_H W1) mem1 (shadow_addr F + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + SU_XO <= a < F + SU_XO + 136) ->
 ~ (shadow_addr F + 88 <= a < shadow_addr F + 105) ->
 aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) /\
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) memc a <> None -> aview rsegs (w_H W1) mem1 a <> None).

Lemma su_A : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R F pos : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> frame_addr lyc 4 pos = F ->
getr regs (Z_to_bv 5 2) = w64 R -> getr regs (Z_to_bv 5 3) = w64 (as_gp B) ->
getr regs (Z_to_bv 5 4) = w64 (as_tp B) ->
getr regs (Z_to_bv 5 19) = w64 (shadow_addr F) -> getr regs (Z_to_bv 5 21) = w64 F ->
R mod 32 = 0 -> R + 0x220 <= sp0 -> sp0 - STK <= R - ASTACK ->
(forall ly1 S1 W1 regs1 mem1 md1,
 su_A_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F ly1 S1 W1 regs1 mem1 md1 ->
 SRr rsegs W1 (cfg_at rsegs 0x83034 regs1 mem1 md1) Q) ->
SRr rsegs W (cfg_at rsegs 0x82fdc regs memc mdc) Q.
Proof using MTL AMEMSET.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos Q
  HJ Hown HF H2 H3 H4 H19 H21 HR32 HRS HRstk K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & Hly0 & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF32 & HFapp & HFb & HFsh).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFc & _).
rewrite HF in HF32, HFapp, HFb, HFsh, HF4096, HFc.
change (fs_frame_bytes 4) with 1024 in HFapp, HFb, HFsh, HFc.
change (1024 / 8) with 128 in HFsh.
pose proof (@ASAN_CEIL_range rc) as Hceil. unfold ASAN_CEIL in Hceil.
unfold ASTACK in HRstk.
assert (HxR : F + 0x348 <= R - ESTACK) by (unfold ESTACK in *; lia).
assert (HRc : alloc_ceiling + 16384 <= R) by lia.
assert (HshA : 0 <= shadow_addr F /\ shadow_addr F + 128 <= 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. split; lia. }
assert (HshR : shadow_addr F + 128 <= R - ESTACK)
  by (unfold shadow_addr, SHADOW_OFF, ESTACK in *; lia).
assert (Hxsh : shadow_addr F + 128 <= F + 0x2c0 \/ F + 0x348 <= shadow_addr F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *.
  destruct HFapp as [_ [HA|[HA1 HA2]]]; [right | left]; lia. }
(* ---- the one instruction 0x82fdc: s2 := F + 0x2c0 ---- *)
set (E0 := Ereg regs []).
assert (E21 : ew E0 21 = Z_to_bv 64 F)
  by (exact (eq_trans (ew_Ereg_nat regs [] 21 (Z_to_bv 5 21) eq_refl) H21)).
assert (HS0 : st_ok rsegs E0 (mkSS 0x82fdc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82fdc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
assert (HAE0 : env_agree 32 (Ereg regs []) E0) by (subst E0; apply env_agree_refl).
unfold cfg_at. change (w64 0x82fdc) with (Z_to_bv 64 0x82fdc).
aj_run_to su_tblA_ok HS0 HJ 0x82fe0; [apply awr_ok_nil|].
cbn [ms_mem mkst] in HJ.
assert (HmemA : ms_mem ms = memc).
{ cbn [ss_mem] in HF0. exact (frame_of_read_only E0 [] memc (ms_mem ms) eq_refl HF0). }
assert (RA18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (F + SU_XO)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS0). su_sv.
  rewrite (su_soff E0 21 F 704 E21). unfold w64, SU_XO. f_equal; lia. }
assert (RAk : forall r : Z, 0 < r < 32 -> r <> 18 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr Hn18.
  assert (Hu : bv_unsigned (Z_to_bv 5 r) = r)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32;
        apply Z.mod_small; lia).
  apply (HPgSteps.regs_kept_of_st_ok rsegs E0 _ _ regs [] (w_H W) [(18%bv : bv 5)] HS0 HAE0
    ltac:(vm_compute; reflexivity)); [rewrite Hu; lia|].
  cbn [In]. intros [HH|[]]. apply (f_equal (@bv_unsigned 5)) in HH. rewrite Hu in HH.
  vm_compute (bv_unsigned (18%bv : bv 5)) in HH. lia. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS0 eq_refl) as EmsA. cbn [ss_pc] in EmsA.
rewrite HmemA in HJ. rewrite EmsA, HmemA.
set (regsA := ms_regs ms) in *.
match goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdA := m) in * end.
assert (HioA : same_io mdc mdA) by (unfold mdA; apply same_io_wvb).
clearbody regsA mdA. clear EmsA HmemA HS0 HF0 HFr HG ms.
(* ---- x's seventeen shadow granules: hdu_scope_x_in ---- *)
eapply SRr_bind.
{ exact (hdu_scope_x_in B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdA k regsA 4 pos
    HJ Hown ltac:(lia)
    ltac:(rewrite <- (su_getr_z regsA (19%bv : bv 5) 19 eq_refl), (RAk 19 ltac:(lia) ltac:(lia)),
            HF; exact H19)
    ltac:(rewrite HF; lia)
    ltac:(rewrite HF; lia)
    ltac:(change (fs_frame_bytes 4 / 8) with 128; lia)). }
cbv beta.
intros W1 c1 Hle1 (ly1 & S1 & regsB & memB & mdB & -> & HJ1 & Hkp1 & Hfr1 & Hpm1 & Hio1 & Hmo1 & Hkeep1 & Hsh1).
rewrite HF in Hkeep1, Hsh1.
pose proof HJ1 as (HAR1 & Hly1 & _).
assert (HF1 : frame_addr ly1 4 pos = F)
  by (rewrite <- HF; exact (su_frame_addr_le _ ly ly1 lyc 4 pos Hly1 Hly0)).
assert (Hkp1' : forall r : Z, 0 < r < 32 -> getr regsB (Z_to_bv 5 r) = getr regsA (Z_to_bv 5 r)).
{ intros r Hr. apply Hkp1; [|cbn [In]; tauto].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Z.mod_small by lia. lia. }
(* ---- 0x83024 .. the `jal` of the memset ---- *)
set (E1 := Ereg regsB []).
assert (HS1 : st_ok rsegs E1 (mkSS 0x83024 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W1) (mkst regsB (Z_to_bv 64 0x83024) memB (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
assert (HAE1 : env_agree 32 (Ereg regsB []) E1) by (subst E1; apply env_agree_refl).
assert (E1_18 : ew E1 18 = Z_to_bv 64 (F + SU_XO)).
{ refine (eq_trans (ew_Ereg_nat regsB [] 18 (Z_to_bv 5 18) eq_refl) _).
  rewrite (Hkp1' 18 ltac:(lia)). exact RA18. }
unfold cfg_at. change (w64 0x83024) with (Z_to_bv 64 0x83024).
aj_run_to su_tblC_ok HS1 HJ1 B_ASAN_MEMSET; [apply awr_ok_nil|].
cbn [ms_mem mkst] in HJ1.
assert (HmemB : ms_mem ms = memB).
{ cbn [ss_mem] in HF0. exact (frame_of_read_only E1 [] memB (ms_mem ms) eq_refl HF0). }
assert (RB1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 0x83034)
  by (rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS1); su_sv; reflexivity).
assert (RB10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (F + SU_XO))
  by (rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS1); su_sv;
      rewrite (su_soff E1 18 (F + SU_XO) 0 E1_18); unfold w64; f_equal; lia).
assert (RB11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 0)
  by (rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS1); su_sv; reflexivity).
assert (RB12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 136)
  by (rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS1); su_sv; reflexivity).
assert (RBk : forall r : Z, 0 < r < 32 -> r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regsB (Z_to_bv 5 r)).
{ intros r Hr H1' H10' H11' H12'.
  assert (Hu : bv_unsigned (Z_to_bv 5 r) = r)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32;
        apply Z.mod_small; lia).
  apply (HPgSteps.regs_kept_of_st_ok rsegs E1 _ _ regsB [] (w_H W1)
    [(1%bv : bv 5); (10%bv : bv 5); (11%bv : bv 5); (12%bv : bv 5)] HS1 HAE1
    ltac:(vm_compute; reflexivity)); [rewrite Hu; lia|].
  cbn [In]. intros HH.
  repeat (destruct HH as [HH|HH];
    [apply (f_equal (@bv_unsigned 5)) in HH; rewrite Hu in HH; vm_compute in HH; lia|]).
  exact HH. }
assert (Hkr : forall r : Z, 0 < r < 32 -> r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 18 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr Ha Hb Hc Hd He. rewrite (RBk r) by lia. rewrite (Hkp1' r) by lia.
  apply RAk; lia. }
(* the frame's whole shadow row still reads *)
assert (Hrow : forall i, 0 <= i < 128 -> aview rsegs (w_H W1) memB (shadow_addr F + i) <> None).
{ intros i Hi. destruct (Z.le_gt_cases 88 i) as [Hi1|Hi1]; [destruct (Z.lt_ge_cases i 105) as [Hi2|Hi2]|].
  - rewrite (Hsh1 i ltac:(lia)). discriminate.
  - rewrite Hkeep1 by lia. apply su_aview_some. exact (proj1 (HFsh i ltac:(lia))).
  - rewrite Hkeep1 by lia. apply su_aview_some. exact (proj1 (HFsh i ltac:(lia))). }
pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS1 eq_refl) as EmsB. cbn [ss_pc] in EmsB.
rewrite HmemB in HJ1. rewrite EmsB, HmemB.
set (regsC := ms_regs ms) in *.
match goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdC := m) in * end.
assert (HioC : same_io mdB mdC) by (unfold mdC; apply same_io_wvb).
clearbody regsC mdC. clear EmsB HmemB HS1 HF0 HFr HG ms.
(* ---- the call __asan_memset(x, 0, 136) ---- *)
eapply SRr_bind.
{ apply (hdu_memset_at B (AMEMSET fx) W1 regsC memB STK sp0 FP ly S W0 mem0 md0 own ly1 S1
    mdC k (F + SU_XO) 0 136 (R - sp0) (Z_to_bv 64 0x83034) HJ1).
  - rewrite <- (su_getr_z regsC (10%bv : bv 5) 10 eq_refl). exact RB10.
  - rewrite <- (su_getr_z regsC (11%bv : bv 5) 11 eq_refl). exact RB11.
  - rewrite <- (su_getr_z regsC (12%bv : bv 5) 12 eq_refl). exact RB12.
  - lia.
  - unfold SU_XO. lia.
  - unfold SU_XO. lia.
  - unfold spZ. rewrite <- (su_getr_z regsC (2%bv : bv 5) 2 eq_refl), (Hkr 2 ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), H2. unfold w64.
    rewrite unsigned_lit_small by lia. ring.
  - lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite <- (su_getr_z regsC (3%bv : bv 5) 3 eq_refl), (Hkr 3 ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact H3.
  - rewrite <- (su_getr_z regsC (4%bv : bv 5) 4 eq_refl), (Hkr 4 ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact H4.
  - rewrite <- (su_getr_z regsC (1%bv : bv 5) 1 eq_refl). exact RB1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + right. right. right. exists 4, pos. split; [exact Hown|]. left.
      unfold in_zr. cbn [fst snd]. rewrite HF1.
      change (fs_frame_bytes 4) with 1024. unfold SU_XO in *. lia.
    + unfold ESTACK, SU_XO in *. lia.
  - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SU_XO in *. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr F + (x / 8 - F / 8))
      by (unfold shadow_of_addr, shadow_addr; ring).
    apply Hsh1. unfold SU_XO in *. lia.
  - intros _ s Hs. unfold SU_XO in Hs.
    replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
    apply Hrow. unfold shadow_addr, SHADOW_OFF in *. lia. }
cbv beta.
intros W2 c2 Hle2 (-> & regsD & memD & mdD & -> & HJ2 & Hio2 & Hpr2 & Ha0 & Hset & Hkeep2 & Hgrow2).
apply (K ly1 S1 W1 regsD memD mdD).
red. split; [exact HJ2|].
split; [exact Hfr1|]. split; [exact Hpm1|].
split; [eapply same_io_trans; [exact HioA|]; eapply same_io_trans; [exact Hio1|];
        eapply same_io_trans; [exact HioC | exact Hio2]|].
split; [exact Hmo1|].
split; [exact Hly1|].
split.
{ intros r Hr. cbn [In] in Hr.
  rewrite (Hpr2 r ltac:(unfold acallee_saved; lia)).
  apply Hkr; lia. }
split.
{ rewrite (Hpr2 18 ltac:(unfold acallee_saved; lia)).
  rewrite (RBk 18) by lia. rewrite (Hkp1' 18) by lia. exact RA18. }
split; [intros i Hi; rewrite (Hset i Hi); reflexivity|].
split.
{ intros i Hi. rewrite Hkeep2.
  - apply Hsh1. exact Hi.
  - lia.
  - unfold SU_XO in *. lia.
  - unfold ESTACK in *. lia. }
split.
{ intros a Ha H1' H2' H3'. rewrite Hkeep2 by (unfold ESTACK in *; lia).
  apply Hkeep1. lia. lia. }
intros a Ha Hv.
apply (su_aview_grows (w_H W1) memB memD Hgrow2).
destruct (Z.le_gt_cases (shadow_addr F + 88) a) as [Hb1|Hb1];
[destruct (Z.lt_ge_cases a (shadow_addr F + 105)) as [Hb2|Hb2]|].
- replace a with (shadow_addr F + (a - shadow_addr F)) by ring.
  rewrite (Hsh1 (a - shadow_addr F) ltac:(lia)). discriminate.
- rewrite Hkeep1 by lia. exact Hv.
- rewrite Hkeep1 by lia. exact Hv.
Qed.
End blk.

Ltac su_awr U9 d :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat d);
  [reflexivity | cbn [base_val]; rewrite U9; lia | cbn; lia | cbn; lia | ] ].
Ltac su_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac su_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
Ltac su_keepstep HFr U9r :=
  intros a Ha Hn; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
  rewrite unsigned_lit_small by exact Ha;
  intros (rg & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<-|Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi su_rR su_rP base_val] in Hr;
     first [rewrite U9r in Hr; apply Hn; lia | lia] | ]); destruct Hin.

Definition su_B_keep (R : Z) (W1 : world rsegs) (mem1 mem3 : word -> option byte) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x98 <= a < R + 0x140) ->
   aview rsegs (w_H W1) mem3 a = aview rsegs (w_H W1) mem1 a) /\
(forall a, aview rsegs (w_H W1) mem1 a <> None -> aview rsegs (w_H W1) mem3 a <> None).
Definition su_B_kept (regs1 regs3 : bvmap 5 word) : Prop :=
forall r : Z, In r [2; 3; 4; 8; 9; 19; 20; 22; 25; 26; 27] ->
getr regs3 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r).

Section blkB. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Definition su_B_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (ly1 : alayout) (S1 : astate)
(W1 : world rsegs) (mem1 : word -> option byte) (md1 : Model) (k : Z) (regs1 : bvmap 5 word) (R : Z)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem3 md3 k /\
same_io md1 md3 /\ su_B_keep R W1 mem1 mem3 /\ su_B_kept regs1 regs3.

(* what the pair head reads: the loop's constants and the entry table's addresses *)
Definition su_B_cells (W1 : world rsegs) (mem3 : word -> option byte) (R F pp : Z) : Prop :=
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0x98) 8 ((pp + 0x4d14) mod 8 + 3) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0xa0) 8 0xbffe000000000000 /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0xa8) 8 0x3ffe000000000000 /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0xb0) 8 0xc03e000000000000 /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0xb8) 8 (2 ^ 49) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0xc0) 8 ((-1 - (F + SU_XO + 4)) mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0xc8) 8 (F + SU_XO + 4) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0xd0) 8 1000000 /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0x118) 8 (0xd * 2 ^ 35) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0x120) 8 (pp + 0x4d14) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0x128) 8 ((-1 - (pp + 0x401c)) mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0x130) 8 (shadow_addr (pp + 0x4d14)) /\
val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0x138) 8 (F + SU_XO).
Definition su_B_regs (pp : Z) (regs3 : bvmap 5 word) : Prop :=
getr regs3 (Z_to_bv 5 5) = w64 (pp + 0x4014) /\ getr regs3 (Z_to_bv 5 6) = w64 (pp + 0x4018) /\
getr regs3 (Z_to_bv 5 7) = w64 ((-1 - (pp + 0x4014)) mod 2 ^ 64) /\
getr regs3 (Z_to_bv 5 12) = w64 0 /\ getr regs3 (Z_to_bv 5 21) = w64 8 /\
getr regs3 (Z_to_bv 5 28) = w64 (pp + 0x401c) /\ getr regs3 (Z_to_bv 5 29) = w64 (pp + 0x401c) /\
getr regs3 (Z_to_bv 5 30) = w64 (pp + 0x4010) /\
getr regs3 (Z_to_bv 5 31) = w64 (shadow_addr (pp + 0x4010)).

Lemma su_B : forall STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k (regs1 : bvmap 5 word)
(R F pp : Z) (nl ip ps : bool) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
In (pp, 19744) (ablocks B ly1 S1) ->
getr regs1 (Z_to_bv 5 9) = w64 R -> getr regs1 (Z_to_bv 5 18) = w64 (F + SU_XO) ->
getr regs1 (Z_to_bv 5 21) = w64 F -> getr regs1 (Z_to_bv 5 23) = w64 (if nl then 0 else 1) ->
getr regs1 (Z_to_bv 5 27) = w64 SHADOW_OFF ->
R mod 32 = 0 -> R + 0x220 <= sp0 -> sp0 - STK <= R - ASTACK ->
4096 <= F -> F + 1024 <= alloc_ceiling ->
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 0x8) 8 (pp + 0x4008) ->
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 0xe0) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 0x108) 8 ((-16381) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 0x120) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 0x148) 8 pp ->
val_mem rsegs (mrestrict (w_H W1) mem1) (pp + 0x4008) 4 (Z.b2z ip) ->
val_mem rsegs (mrestrict (w_H W1) mem1) (pp + 0x4010) 4 (Z.b2z ps) ->
(forall regs3 mem3 md3,
 su_B_post STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R regs3 mem3 md3 ->
 getr regs3 (Z_to_bv 5 13) = w64 (-1) ->
 getr regs3 (Z_to_bv 5 18) = getr regs1 (Z_to_bv 5 18) ->
 getr regs3 (Z_to_bv 5 21) = getr regs1 (Z_to_bv 5 21) ->
 (nl = true \/ ip = false) ->
 SRr rsegs W1 (@cfg_at fx rsegs 0x8385c regs3 mem3 md3) Q) ->
(forall regs3 mem3 md3,
 su_B_post STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R regs3 mem3 md3 ->
 val_mem rsegs (mrestrict (w_H W1) mem3) (R + 0x138) 8 (F + SU_XO) ->
 nl = false -> ip = true -> ps = false ->
 SRr rsegs W1 (@cfg_at fx rsegs 0x83850 regs3 mem3 md3) Q) ->
(forall regs3 mem3 md3,
 su_B_post STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R regs3 mem3 md3 ->
 su_B_cells W1 mem3 R F pp -> su_B_regs pp regs3 ->
 nl = false -> ip = true -> ps = true ->
 SRr rsegs W1 (@cfg_at (su_fx3 fx) rsegs 0x8314c regs3 mem3 md3) Q) ->
SRr rsegs W1 (@cfg_at fx rsegs 0x83034 regs1 mem1 md1) Q.
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R F pp nl ip ps Q
  HJ HPP H9 H18 H21 H23 H27 HR32 HRS HRstk HF0 HFc V8 VE0 V108 V120 V148 Vip Vps KRCM KRC KPAIR.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp 19744 HAR HPP) as (Hp16 & Hp4096 & Hpc & Happ & Hpb & _).
change (req_size 19744) with 19744 in Hpc, Happ, Hpb.
pose proof (@ASAN_CEIL_range rc) as Hceil. unfold ASAN_CEIL in Hceil, Happ.
unfold ASTACK in HRstk.
assert (Hp47 : pp + 0x4d20 <= 2 ^ 47)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg in Happ; lia).
set (E := Ereg regs1 [w64 pp]).
assert (E9 : ew E 9 = Z_to_bv 64 R)
  by (exact (eq_trans (ew_Ereg_nat regs1 [w64 pp] 9 (Z_to_bv 5 9) eq_refl) H9)).
assert (E18 : ew E 18 = Z_to_bv 64 (F + SU_XO))
  by (exact (eq_trans (ew_Ereg_nat regs1 [w64 pp] 18 (Z_to_bv 5 18) eq_refl) H18)).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
  by (exact (eq_trans (ew_Ereg_nat regs1 [w64 pp] 27 (Z_to_bv 5 27) eq_refl) H27)).
assert (E32 : ew E 32 = Z_to_bv 64 pp) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs1 [w64 pp]) E) by (subst E; apply env_agree_refl).
assert (U9' : bv_unsigned (ew (Ereg regs1 [w64 pp]) 9) = R) by exact U9.
assert (U32' : bv_unsigned (ew (Ereg regs1 [w64 pp]) 32) = pp) by exact U32.
(* the real frame's region and the first block's region *)
assert (HrR : region_ok rsegs E (mrestrict (w_H W1) mem1) su_rR).
{ unfold su_rR. apply (hm_rw_region rsegs E (w_H W1) mem1 9 R 0x8 0x150 0x98 0x140);
  [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
  repeat apply Forall_cons; [..|apply Forall_nil].
  - apply (chunk_ok_val rsegs E _ R 0x8 8 _ (pp + 0x4008));
    [apply (su_soff E 32 pp 0x4008 E32) | cbn; lia | lia | exact V8].
  - apply (chunk_ok_val rsegs E _ R 0xe0 8 _ (Z.shiftr (pp + 0x4d14) 3)); [| | lia | exact VE0].
    + rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SOff, U_SLit, U32. cbn [zalu_raw].
      unfold zcanon, M64. rewrite (Z.mod_small (pp + 0x4d14)) by lia.
      change (3 mod 2 ^ 64) with 3. change (Z.land 3 63) with 3. apply Z.mod_small.
      rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  - apply (chunk_ok_val rsegs E _ R 0x108 8 _ ((-16381) mod 2 ^ 64));
    [cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
     change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity
    | cbn; lia | lia | exact V108].
  - apply (chunk_ok_val rsegs E _ R 0x120 8 _ (pp + 0x4d14));
    [apply (su_soff E 32 pp 0x4d14 E32) | cbn; lia | lia | exact V120].
  - apply (chunk_ok_val rsegs E _ R 0x148 8 _ pp);
    [rewrite (su_soff E 32 pp 0 E32), Z.add_0_r; reflexivity | cbn; lia | lia | exact V148]. }
assert (HrP : forall cs, Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W1) mem1) pp) cs ->
  region_ok rsegs E (mrestrict (w_H W1) mem1) (su_rP cs)).
{ intros cs Hcs. apply (hm_ro_region rsegs E (w_H W1) mem1 32 pp 0x4008 0x4d18);
  [exact U32 | lia | lia | exact Hcs]. }
assert (Cip : YP09.chunk_ok rsegs E (mrestrict (w_H W1) mem1) pp
  (YP09.mkChunk 0x4008 (CVal 4 (SLit (Z.b2z ip))))).
{ apply (chunk_ok_val rsegs E _ pp 0x4008 4 _ (Z.b2z ip));
  [reflexivity | destruct ip; cbn; lia | lia | exact Vip]. }
assert (Cps : YP09.chunk_ok rsegs E (mrestrict (w_H W1) mem1) pp
  (YP09.mkChunk 0x4010 (CVal 4 (SLit (Z.b2z ps))))).
{ apply (chunk_ok_val rsegs E _ pp 0x4010 4 _ (Z.b2z ps));
  [reflexivity | destruct ps; cbn; lia | lia | exact Vps]. }
assert (HFok : atoms_ok E su_facts).
{ cbn [su_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E27, U32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  repeat split; try lia; apply Z.mod_1_r. }
assert (SHOK : sh_ok rsegs su_Bx su_SH E (mrestrict (w_H W1) mem1)).
{ constructor; [|constructor; [|constructor]].
  - eapply (shent_ok_of_block rsegs B LAWS ly1 S1 W1 mem1 md1 E su_Bx 32 pp 19744 0 0x4d20 HAR HPP).
    + unfold su_Bx. apply U_atom; [exact E27 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E32 | lia].
    + lia.
    + change (req_size 19744) with 19744. lia.
  - eapply shent_app_of_high.
    + unfold su_Bx. apply U_atom; [exact E27 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E9 | lia].
    + unfold kHighMemBeg. lia.
    + lia. }
assert (HB : forall nz cs, regions_wf [su_rR; su_rP cs] = true ->
  getr regs1 (Z_to_bv 5 23) = w64 nz ->
  Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W1) mem1) pp) cs ->
  st_ok rsegs E (su_ssB nz cs)
    (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 0x83034) mem1 (seg_rom rsegs)))).
{ intros nz cs Hwf Hnz Hcs. rewrite restrict_mkst_fx.
  refine (st_ok_pin_lit rsegs E (mkSS 0x83034 sr_atoms [su_rR; su_rP cs] None (mkFacts su_facts [] []))
    _ (Z_to_bv 5 23) nz _ _ _).
  - apply (entry_st_ok_full rsegs).
    + apply regs_ok_Ereg.
    + exact Hwf.
    + apply Forall_cons; [exact HrR | apply Forall_cons; [apply HrP; exact Hcs | apply Forall_nil]].
    + apply pairwise_disjoint_of_extents. unfold su_rR, su_rP.
      cbn [map zpairwise_disjoint zall_disjoint].
      unfold extent_of_region, zdisj. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U9', U32'. lia.
    + split; [exact HFok | split; exact I].
  - vm_compute. reflexivity.
  - cbn [ms_regs mkst]. exact Hnz. }
clearbody E.
unfold cfg_at. change (w64 0x83034) with (Z_to_bv 64 0x83034).
destruct nl.
- (* the null flag is 1: s7 = 0, straight to RCM *)
  pose proof (HB 0 [] ltac:(vm_compute; reflexivity) H23 ltac:(apply Forall_nil)) as HS.
  aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x8385c; [su_awr U9 (R - sp0) | ].
  assert (Hk : forall r : bv 5, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) ->
    getr (ms_regs ms) r = getr regs1 r)
    by (exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs1 [w64 pp]
         (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) HS HAE
         ltac:(vm_compute; reflexivity))).
  pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems.
  apply (KRCM (ms_regs ms) (ms_mem ms) _).
  + split; [exact HJ|].
    split; [apply same_io_wvb|].
    split.
    * split.
      -- intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
         rewrite unsigned_lit_small by exact Ha.
         intros (rg & Hin & Hr). cbn [In] in Hin.
         destruct Hin as [<-|[<-|[]]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi su_rR su_rP base_val] in Hr;
         [rewrite U9 in Hr; apply Hn; lia | lia].
      -- intros a. apply (su_aview_grows_m (w_H W1) mem1 (ms_mem ms) HG).
    * intros r Hr. apply Hk, in_map. cbn [In] in Hr |- *. tauto.
  + rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS). su_sv. cbn [sv_denot]. exact lit_m1.
  + apply Hk, in_map. cbn [In]. tauto.
  + apply Hk, in_map. cbn [In]. tauto.
  + left. reflexivity.
- destruct ip.
  + destruct ps.
    * (* the main path: the constants and the three `fmv.w.x`, to the pair head *)
      pose proof (HB 1 [YP09.mkChunk 0x4008 (CVal 4 (SLit 1)); YP09.mkChunk 0x4010 (CVal 4 (SLit 1))]
        ltac:(vm_compute; reflexivity) H23
        ltac:(apply Forall_cons; [exact Cip | apply Forall_cons; [exact Cps | apply Forall_nil]])) as HS.
      aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x830cc; [su_awr U9 (R - sp0) | ].
      assert (R17 : low32 (getr (ms_regs ms) (Z_to_bv 5 17)) = Z_to_bv 32 0xbf800000)
        by (rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS); su_sv; cbn [sv_denot];
            apply bv_eq; vm_compute; reflexivity).
      pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
      rewrite Ems in HS, SHOK |- *.
      set (rB := ms_regs ms) in *. set (mB := ms_mem ms) in *. clearbody rB mB.
      rename HFr into HFrB. rename HG into HGB. rename HF into HFB. clear Ems ms.
      eapply (su_fmv fx W1 _ _ rB mB _ Q 0x830cc _ 9 17 0xbf800000 _ _ HS);
        [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
        | vm_refl_bv | exact R17 |].
      intros X1 HS1.
      pose proof (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
      clear HJ.
      aj_run_to_tok su_tblB_ok HS1 HJ1 SHOK su_Bspan 0x830d4; [su_awr U9 (R - sp0) | ].
      assert (R5 : low32 (getr (ms_regs ms) (Z_to_bv 5 5)) = Z_to_bv 32 0x43800000)
        by (rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS1); su_sv; cbn [sv_denot];
            apply bv_eq; vm_compute; reflexivity).
      pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS1 eq_refl) as Ems. cbn [ss_pc] in Ems.
      rewrite Ems in HS1, SHOK |- *.
      set (rC := ms_regs ms) in *. set (mC := ms_mem ms) in *. clearbody rC mC.
      rename HFr into HFrC. rename HG into HGC. rename HF into HFC. clear Ems ms.
      eapply (su_fmv _ W1 _ _ rC mC _ Q 0x830d4 _ 18 5 0x43800000 _ _ HS1);
        [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
        | vm_refl_bv | exact R5 |].
      intros X2 HS2.
      pose proof (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJ1) as HJ2.
      clear HJ1.
      aj_run_to_tok su_tblB_ok HS2 HJ2 SHOK su_Bspan 0x830e0; [su_awr U9 (R - sp0) | ].
      assert (R6 : low32 (getr (ms_regs ms) (Z_to_bv 5 6)) = Z_to_bv 32 0x5f000000)
        by (rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS2); su_sv; cbn [sv_denot];
            apply bv_eq; vm_compute; reflexivity).
      pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS2 eq_refl) as Ems. cbn [ss_pc] in Ems.
      rewrite Ems in HS2, SHOK |- *.
      set (rD := ms_regs ms) in *. set (mD := ms_mem ms) in *. clearbody rD mD.
      rename HFr into HFrD. rename HG into HGD. rename HF into HFD. clear Ems ms.
      eapply (su_fmv _ W1 _ _ rD mD _ Q 0x830e0 _ 19 6 0x5f000000 _ _ HS2);
        [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
        | vm_refl_bv | exact R6 |].
      intros X3 HS3.
      pose proof (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJ2) as HJ3.
      clear HJ2.
      aj_run_to_tok su_tblB_ok HS3 HJ3 SHOK su_Bspan 0x8314c; [su_awr U9 (R - sp0) | ].
      assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x98 <= a < R + 0x140) ->
        aview rsegs (w_H W1) mB a = aview rsegs (w_H W1) mem1 a) by su_keepstep HFrB U9.
      assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x98 <= a < R + 0x140) ->
        aview rsegs (w_H W1) mC a = aview rsegs (w_H W1) mB a) by su_keepstep HFrC U9.
      assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x98 <= a < R + 0x140) ->
        aview rsegs (w_H W1) mD a = aview rsegs (w_H W1) mC a) by su_keepstep HFrD U9.
      assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x98 <= a < R + 0x140) ->
        aview rsegs (w_H W1) (ms_mem ms) a = aview rsegs (w_H W1) mD a) by su_keepstep HFr U9.
      assert (Hk : forall r : bv 5, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 22; 25; 26; 27]) ->
        getr (ms_regs ms) r = getr regs1 r)
        by (exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs1 [w64 pp]
             (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 22; 25; 26; 27]) HS3 HAE
             ltac:(vm_compute; reflexivity))).
      pose proof (st_ok_region_at _ _ _ 0%nat _ HS3 ltac:(vm_compute; reflexivity)) as HRok.
      destruct HRok as (_ & _ & _ & Hch).
      cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite U9 in Hch.
      assert (HX : 0 <= F + SU_XO + 4 < 2 ^ 64) by (unfold SU_XO; lia).
      assert (HPn : 0 <= pp + 0x4d14 < 2 ^ 64) by lia.
      pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS3 eq_refl) as Ems. cbn [ss_pc] in Ems.
      rewrite Ems.
      apply (KPAIR (ms_regs ms) (ms_mem ms) _).
      -- split; [exact HJ3|]. split; [su_io|].
         split.
         ++ split.
            ** intros a Ha Hn. rewrite (KE a Ha Hn), (KD a Ha Hn), (KC a Ha Hn). exact (KB a Ha Hn).
            ** intros a Hv.
               apply (su_aview_grows_m (w_H W1) mD (ms_mem ms) HG).
               apply (su_aview_grows_m (w_H W1) mC mD HGD).
               apply (su_aview_grows_m (w_H W1) mB mC HGC).
               apply (su_aview_grows_m (w_H W1) mem1 mB HGB). exact Hv.
         ++ intros r Hr. apply Hk, in_map. cbn [In] in Hr |- *. tauto.
      -- split.
         { apply (su_cell E _ R _ 0x98 (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0x4d14) (SLit 7)) (SLit 3))
             ((pp + 0x4d14) mod 8 + 3) Hch ltac:(su_in)); [|lia].
           rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
           rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E 32 pp 0x4d14 E32 ltac:(lia) ltac:(lia)).
           rewrite !U_SLit. unfold zcanon, M64. change (7 mod 2 ^ 64) with 7. change (3 mod 2 ^ 64) with 3.
           rewrite su_land7 by lia. rewrite (Z.mod_small ((pp + 0x4d14) mod 8)) by lia.
           apply Z.mod_small. lia. }
         split.
         { apply (su_cell E _ R _ 0xa0 (SLit 13834495105328742400) 0xbffe000000000000 Hch
             ltac:(su_in)); [cbn [sv_denot]; reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0xa8 (SLit 4611123068473966592) 0x3ffe000000000000 Hch
             ltac:(su_in)); [cbn [sv_denot]; reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0xb0 (SLit 13852509503838224384) 0xc03e000000000000 Hch
             ltac:(su_in)); [cbn [sv_denot]; reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0xb8 (SLit 562949953421312) (2 ^ 49) Hch
             ltac:(su_in)); [cbn [sv_denot]; reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0xc0 (SAlu ALU_XOR (SOff 18 4) (SLit (-1)))
             ((-1 - (F + SU_XO + 4)) mod 2 ^ 64) Hch ltac:(su_in));
           [|rewrite su_notmod by lia; lia].
           rewrite denot_lit_U. f_equal.
           rewrite (U_not_off E 18 (F + SU_XO) 4 E18 ltac:(unfold SU_XO; lia) ltac:(lia)).
           rewrite su_notmod by lia. reflexivity. }
         split.
         { apply (su_cell E _ R _ 0xc8 (SOff 18 4) (F + SU_XO + 4) Hch ltac:(su_in));
           [rewrite (su_soff E 18 (F + SU_XO) 4 E18); reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0xd0 (SLit 1000000) 1000000 Hch
             ltac:(su_in)); [cbn [sv_denot]; reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0x118 (SLit 446676598784) (0xd * 2 ^ 35) Hch
             ltac:(su_in)); [cbn [sv_denot]; reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0x120 (SOff 32 0x4d14) (pp + 0x4d14) Hch ltac:(su_in));
           [rewrite (su_soff E 32 pp 0x4d14 E32); reflexivity | lia]. }
         split.
         { apply (su_cell E _ R _ 0x128 (SAlu ALU_SUB (SLit 0) (SOff 32 16413))
             ((-1 - (pp + 0x401c)) mod 2 ^ 64) Hch ltac:(su_in));
           [|pose proof (Z.mod_pos_bound (-1 - (pp + 0x401c)) (2 ^ 64) ltac:(lia)); lia].
           rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
           rewrite U_SLit, (U_atom_off E 32 pp 16413 E32 ltac:(lia) ltac:(lia)).
           unfold zcanon, M64. change (0 mod 2 ^ 64) with 0. f_equal. lia. }
         split.
         { apply (su_cell E _ R _ 0x130
             (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0x4d14) (SLit 3)) (SOff 27 0))
             (shadow_addr (pp + 0x4d14)) Hch ltac:(su_in));
           [|unfold shadow_addr, SHADOW_OFF; lia].
           rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
           rewrite U_SAlu. cbn [zalu_raw].
           rewrite (U_atom_off E 32 pp 0x4d14 E32 ltac:(lia) ltac:(lia)), U_SLit.
           rewrite (U_atom E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)).
           unfold zcanon, M64, shadow_addr, SHADOW_OFF.
           change (3 mod 2 ^ 64) with 3. change (Z.land 3 63) with 3.
           rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
           rewrite (Z.mod_small ((pp + 0x4d14) / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
           assert (Hd8 : (pp + 0x4d14) / 8 <= pp + 0x4d14) by (apply Z.div_le_upper_bound; lia).
           rewrite Z.mod_small by lia. lia. }
         { apply (su_cell E _ R _ 0x138 (SOff 18 0) (F + SU_XO) Hch ltac:(su_in));
           [rewrite (su_soff E 18 (F + SU_XO) 0 E18), Z.add_0_r; reflexivity | unfold SU_XO; lia]. }
      -- unfold su_B_regs.
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  rewrite (su_soff E 32 pp 0x4014 E32). reflexivity. }
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  rewrite (su_soff E 32 pp 0x4018 E32). reflexivity. }
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  rewrite denot_lit_U. unfold w64. f_equal.
                  rewrite (U_not_off E 32 pp 0x4014 E32 ltac:(lia) ltac:(lia)).
                  rewrite su_notmod by lia. reflexivity. }
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  cbn [sv_denot]. reflexivity. }
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  cbn [sv_denot]. reflexivity. }
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  rewrite (su_soff E 32 pp 0x401c E32). reflexivity. }
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  rewrite (su_soff E 32 pp 0x401c E32). reflexivity. }
         split. { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
                  rewrite (su_soff E 32 pp 0x4010 E32). reflexivity. }
         { rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS3). su_sv.
           rewrite denot_lit_U. unfold w64. f_equal.
           rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
           rewrite (U_atom_off E 32 pp 0x4010 E32 ltac:(lia) ltac:(lia)), U_SLit.
           rewrite (U_atom E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)).
           unfold zcanon, M64, shadow_addr, SHADOW_OFF.
           change (3 mod 2 ^ 64) with 3. change (Z.land 3 63) with 3.
           rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
           rewrite (Z.mod_small ((pp + 0x4010) / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
           assert (Hd8 : (pp + 0x4010) / 8 <= pp + 0x4010) by (apply Z.div_le_upper_bound; lia).
           rewrite Z.mod_small by lia. lia. }
      -- reflexivity.
      -- reflexivity.
      -- reflexivity.
    * (* the params property is not a Struct: to RC *)
      pose proof (HB 1 [YP09.mkChunk 0x4008 (CVal 4 (SLit 1)); YP09.mkChunk 0x4010 (CVal 4 (SLit 0))]
        ltac:(vm_compute; reflexivity) H23
        ltac:(apply Forall_cons; [exact Cip | apply Forall_cons; [exact Cps | apply Forall_nil]])) as HS.
      aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x83850; [su_awr U9 (R - sp0) | ].
      assert (Hk : forall r : bv 5, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) ->
        getr (ms_regs ms) r = getr regs1 r)
        by (exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs1 [w64 pp]
             (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) HS HAE
             ltac:(vm_compute; reflexivity))).
      pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
      destruct HRok as (_ & _ & _ & Hch).
      cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite U9 in Hch.
      assert (V138 : val_mem rsegs (mrestrict (w_H W1) (ms_mem ms)) (R + 0x138) 8 (F + SU_XO)).
      { apply (su_cell E _ R _ 0x138 (SOff 18 0) (F + SU_XO) Hch ltac:(su_in));
        [rewrite (su_soff E 18 (F + SU_XO) 0 E18), Z.add_0_r; reflexivity | unfold SU_XO; lia]. }
      pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
      rewrite Ems.
      apply (KRC (ms_regs ms) (ms_mem ms) _).
      -- split; [exact HJ|].
         split; [apply same_io_wvb|].
         split.
         ++ split.
            ** intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
               rewrite unsigned_lit_small by exact Ha.
               intros (rg & Hin & Hr). cbn [In] in Hin.
               destruct Hin as [<-|[<-|[]]];
               cbn [YP09.r_base YP09.r_wlo YP09.r_whi su_rR su_rP base_val] in Hr;
               [rewrite U9 in Hr; apply Hn; lia | lia].
            ** intros a. apply (su_aview_grows_m (w_H W1) mem1 (ms_mem ms) HG).
         ++ intros r Hr. apply Hk, in_map. cbn [In] in Hr |- *. tauto.
      -- exact V138.
      -- reflexivity.
      -- reflexivity.
      -- reflexivity.
  + (* not an Object of Props: to RCM *)
    pose proof (HB 1 [YP09.mkChunk 0x4008 (CVal 4 (SLit 0))]
      ltac:(vm_compute; reflexivity) H23
      ltac:(apply Forall_cons; [exact Cip | apply Forall_nil])) as HS.
    aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x8385c; [su_awr U9 (R - sp0) | ].
    assert (Hk : forall r : bv 5, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) ->
      getr (ms_regs ms) r = getr regs1 r)
      by (exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs1 [w64 pp]
           (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) HS HAE
           ltac:(vm_compute; reflexivity))).
    pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    rewrite Ems.
    apply (KRCM (ms_regs ms) (ms_mem ms) _).
    * split; [exact HJ|].
      split; [apply same_io_wvb|].
      split.
      -- split.
         ++ intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
            rewrite unsigned_lit_small by exact Ha.
            intros (rg & Hin & Hr). cbn [In] in Hin.
            destruct Hin as [<-|[<-|[]]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi su_rR su_rP base_val] in Hr;
            [rewrite U9 in Hr; apply Hn; lia | lia].
         ++ intros a. apply (su_aview_grows_m (w_H W1) mem1 (ms_mem ms) HG).
      -- intros r Hr. apply Hk, in_map. cbn [In] in Hr |- *. tauto.
    * rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms _ HS). su_sv. cbn [sv_denot]. exact lit_m1.
    * apply Hk, in_map. cbn [In]. tauto.
    * apply Hk, in_map. cbn [In]. tauto.
    * right. reflexivity.
Qed.

(* ============ the pair head with no entry: 0x8314c .. RC 0x83850 ============
   n_ent = 0, so `bge a2,a3` at 0x83160 is taken at a2 = 0; the five instructions write nothing. *)
Definition su_tblN : ctable := build_table rsegs 0x8314c 6 TEmpty.
Definition su_tblN_ok : table_ok rsegs su_tblN := build_table_ok0 rsegs 6 0x8314c ltac:(lia).
Definition su_rN : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x120 0x138 0 0
  [ YP09.mkChunk 0x120 (CVal 8 (SOff 32 0x4d14));
    YP09.mkChunk 0x130 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0x4d14) (SLit 3)) (SOff 27 0))) ].
Definition su_rN2 : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x4d14 0x4d18 0 0 [ YP09.mkChunk 0x4d14 (CVal 4 (SLit 0)) ].
Definition su_SHN : list shent := [mkSHE 32 0 0x4d20].
Definition su_ssN : sstate :=
  mkSS 0x8314c (sr_set sr_atoms (Z_to_bv 5 12) (SLit 0)) [su_rN; su_rN2] None (mkFacts su_facts [] []).

Lemma su_N0 : forall STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k (regs1 : bvmap 5 word)
(R pp : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
In (pp, 19744) (ablocks B ly1 S1) ->
getr regs1 (Z_to_bv 5 9) = w64 R -> getr regs1 (Z_to_bv 5 12) = w64 0 ->
getr regs1 (Z_to_bv 5 27) = w64 SHADOW_OFF ->
R + 0x220 <= sp0 -> sp0 - STK <= R - ASTACK ->
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 0x120) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 0x130) 8 (shadow_addr (pp + 0x4d14)) ->
val_mem rsegs (mrestrict (w_H W1) mem1) (pp + 0x4d14) 4 0 ->
(forall regs3 md3,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md3 k -> same_io md1 md3 ->
 (forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27] ->
  getr regs3 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
 SRr rsegs W1 (@cfg_at fx rsegs 0x83850 regs3 mem1 md3) Q) ->
SRr rsegs W1 (@cfg_at fx rsegs 0x8314c regs1 mem1 md1) Q.
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R pp Q
  HJ HPP H9 H12 H27 HRS HRstk V120 V130 Vn K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp 19744 HAR HPP) as (Hp16 & Hp4096 & Hpc & Happ & Hpb & _).
change (req_size 19744) with 19744 in Hpc, Happ, Hpb.
pose proof (@ASAN_CEIL_range rc) as Hceil. unfold ASAN_CEIL in Hceil, Happ.
unfold ASTACK in HRstk.
assert (Hp47 : pp + 0x4d20 <= 2 ^ 47)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg in Happ; lia).
set (E := Ereg regs1 [w64 pp]).
assert (E9 : ew E 9 = Z_to_bv 64 R)
  by (exact (eq_trans (ew_Ereg_nat regs1 [w64 pp] 9 (Z_to_bv 5 9) eq_refl) H9)).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
  by (exact (eq_trans (ew_Ereg_nat regs1 [w64 pp] 27 (Z_to_bv 5 27) eq_refl) H27)).
assert (E32 : ew E 32 = Z_to_bv 64 pp) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs1 [w64 pp]) E) by (subst E; apply env_agree_refl).
assert (U9' : bv_unsigned (ew (Ereg regs1 [w64 pp]) 9) = R) by exact U9.
assert (U32' : bv_unsigned (ew (Ereg regs1 [w64 pp]) 32) = pp) by exact U32.
assert (HFok : atoms_ok E su_facts).
{ cbn [su_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E27, U32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  repeat split; try lia; apply Z.mod_1_r. }
assert (SHOK : sh_ok rsegs su_Bx su_SHN E (mrestrict (w_H W1) mem1)).
{ constructor; [|constructor].
  eapply (shent_ok_of_block rsegs B LAWS ly1 S1 W1 mem1 md1 E su_Bx 32 pp 19744 0 0x4d20 HAR HPP).
  - unfold su_Bx. apply U_atom; [exact E27 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E32 | lia].
  - lia.
  - change (req_size 19744) with 19744. lia. }
assert (HS : st_ok rsegs E su_ssN
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 0x8314c) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx.
  refine (st_ok_pin_lit rsegs E (mkSS 0x8314c sr_atoms [su_rN; su_rN2] None (mkFacts su_facts [] []))
    _ (Z_to_bv 5 12) 0 _ _ _).
  - apply (entry_st_ok_full rsegs).
    + apply regs_ok_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold su_rN. apply (hm_ro_region rsegs E (w_H W1) mem1 9 R 0x120 0x138);
        [exact U9 | lia | lia |].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val rsegs E _ R 0x120 8 _ (pp + 0x4d14));
           [apply (su_soff E 32 pp 0x4d14 E32) | cbn; lia | lia | exact V120].
        -- apply (chunk_ok_val rsegs E _ R 0x130 8 _ (shadow_addr (pp + 0x4d14)));
           [| cbn; unfold shadow_addr, SHADOW_OFF; lia | lia | exact V130].
           rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
           rewrite (U_atom_off E 32 pp 0x4d14 E32 ltac:(lia) ltac:(lia)), U_SLit.
           rewrite (U_atom E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)).
           unfold zcanon, M64, shadow_addr, SHADOW_OFF.
           change (3 mod 2 ^ 64) with 3. change (Z.land 3 63) with 3.
           rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
           rewrite (Z.mod_small ((pp + 0x4d14) / 8))
             by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
           assert (Hd8 : (pp + 0x4d14) / 8 <= pp + 0x4d14) by (apply Z.div_le_upper_bound; lia).
           rewrite Z.mod_small by lia. lia.
      * unfold su_rN2. apply (hm_ro_region rsegs E (w_H W1) mem1 32 pp 0x4d14 0x4d18);
        [exact U32 | lia | lia |].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs E _ pp 0x4d14 4 _ 0); [reflexivity | cbn; lia | lia | exact Vn].
    + apply pairwise_disjoint_of_extents. unfold su_rN, su_rN2.
      cbn [map zpairwise_disjoint zall_disjoint].
      unfold extent_of_region, zdisj. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U9', U32'. lia.
    + split; [exact HFok | split; exact I].
  - vm_compute. reflexivity.
  - cbn [ms_regs mkst]. exact H12. }
clearbody E.
unfold cfg_at. change (w64 0x8314c) with (Z_to_bv 64 0x8314c).
aj_run_to_tok su_tblN_ok HS HJ SHOK su_Bspan 0x83850; [apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
assert (Hmem : ms_mem ms = mem1).
{ cbn [ss_mem] in HF. exact (frame_of_read_only E [su_rN; su_rN2] mem1 (ms_mem ms) eq_refl HF). }
assert (Hk : forall r : bv 5, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) ->
  getr (ms_regs ms) r = getr regs1 r)
  by (exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs1 [w64 pp]
       (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]) HS HAE
       ltac:(vm_compute; reflexivity))).
pose proof (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Hmem in HJ. rewrite Ems, Hmem.
apply (K (ms_regs ms) _).
- exact HJ.
- su_io.
- intros r Hr. apply Hk, in_map. cbn [In] in Hr |- *. tauto.
Qed.
End blkB.

(* the bytes the set-up writes: the callees' stack below R, the frame object x, its shadow granules and the
   real-frame cells the loop's constants go to *)
Definition su_WR (R F : Z) (a : Z) : Prop :=
  (R - ESTACK <= a < R) \/ (F + SU_XO <= a < F + SU_XO + 136) \/
  (shadow_addr F + 88 <= a < shadow_addr F + 105) \/ (R + 0x98 <= a < R + 0x140).

(* x after the memset: 136 zero bytes, which is what the answer (-1 or 0, [], (0, 0, REFUSE_NONE)) asks for *)
Lemma su_x_zero : hd_zbytes (hqu_x_open [] 0 Headamp.REFUSE_NONE) = repeat 0 136.
Proof. vm_compute. reflexivity. Qed.
Lemma su_shX_set : hm_setn headamp_B_shB 88 17 0 = hqu_shX.
Proof. vm_compute. reflexivity. Qed.
(* the two early answers of expect_of (Pod/Headamp.v expect_model) *)
Lemma su_exp_m1 : forall nb cap r, nb = true \/ Model.is_props r = false ->
  Headamp.expect_model nb cap r = (-1, [], (0, 0, Headamp.REFUSE_NONE)).
Proof.
intros nb cap r H. unfold Headamp.expect_model.
destruct H as [->|H]; [reflexivity|]. rewrite H. destruct nb; reflexivity.
Qed.
Lemma su_exp_0 : forall cap r, Model.is_props r = true -> Model.params_struct r = false ->
  Headamp.expect_model false cap r = (0, [], (0, 0, Headamp.REFUSE_NONE)).
Proof. intros cap r H1 H2. unfold Headamp.expect_model. rewrite H1, H2. reflexivity. Qed.
Lemma su_exp_nil : forall cap r, Model.is_props r = true -> Model.params_struct r = true ->
  Model.ents r = [] -> Headamp.expect_model false cap r = (0, [], (0, 0, Headamp.REFUSE_NONE)).
Proof. intros cap r H1 H2 H3. unfold Headamp.expect_model. rewrite H1, H2, H3. reflexivity. Qed.

Lemma su_val_kept : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a n v,
  val_mem rsegs (mrestrict H1 m1) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> aview rsegs H2 m2 (a + i) = aview rsegs H1 m1 (a + i)) ->
  val_mem rsegs (mrestrict H2 m2) a n v.
Proof.
intros H1 H2 m1 m2 a n v V K kk Hk. specialize (V kk Hk).
pose proof (K (Z.of_nat kk) ltac:(lia)) as Eq. unfold aview in Eq. rewrite V in Eq.
destruct (mbyte rsegs (mrestrict H2 m2) (a + Z.of_nat kk)) as [b|] eqn:Eb; [|discriminate Eq].
cbn [option_map] in Eq. injection Eq as Eq. f_equal. apply bv_eq. exact Eq.
Qed.
Lemma su_garr8_kept : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) base l,
  garr8 rsegs (mrestrict H1 m1) base l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview rsegs H2 m2 (base + i) = aview rsegs H1 m1 (base + i)) ->
  garr8 rsegs (mrestrict H2 m2) base l.
Proof.
intros H1 H2 m1 m2 base l G K j Hj. destruct (G j Hj) as [V Hr]. split; [|exact Hr].
apply (su_val_kept H1 H2 m1 m2 (base + Z.of_nat j) 1 (nth j l 0) V).
intros i Hi. assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
apply (K (Z.of_nat j) ltac:(lia)).
Qed.

Section asm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMSET : forall fx' : YK11.FPState, @aintrin_realizes fx' rc rsegs B OSet B_ASAN_MEMSET.

Theorem hqu_M3a_setup : hqu_piece_M3a_setup_stmt rsegs B MT.
Proof using MTL AMEMSET.
unfold hqu_piece_M3a_setup_stmt. intros cx POST r ev Hstart HPAIR HRC HRCM.
unfold hqu_from_X. intros fx2 ly2 S2 W2 regs2 mem2 md2 HX.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
destruct Hstart as (Hpre & HL5 & Hwf & Hlen & Hpp0 & Hpod0 & Hpodf & Hpodra & Hpodh & Hpodm & Hpodal
  & Houtf & Houtra & Hdisj & Hrc & Herrno & Hfrm).
destruct HX as (HB3 & Hat & Hcorr).
destruct HB3 as (Hcore & Hfxk & Hfsh & Hrom & Hppat & Hpodat & Houtat & Hresat & Hev).
destruct Hcore as (HJ & H234 & Hfrs & Hperm & Hio & Hmo & Hkeep).
destruct Hpre as (HJ0 & Hnev & Hsp2 & Hsgp & Hstp & HeS & HR32 & HRsz & HRstk & Hown & HFdef & Hfsh0
  & Hcap & Hnull & Hro & Hglobs & Hrz & Hstrs & Hcells & Hguard & Hrom0 & Hppf).
change (hi_rsz headamp_himg_B) with 0x220 in HRsz.
change (hi_cid headamp_himg_B) with 4 in Hown, HFdef.
pose proof Hat as Hall. unfold hsu_at_cx, hsu_at in Hall. rewrite Forall_forall in Hall.
unfold hqu_L_seg, hqu_L_frame in Hall. rewrite <- !app_assoc in Hall. cbn [app] in Hall.
assert (A2 : getr regs2 (Z_to_bv 5 2) = w64 (e_R (x_e rsegs cx))).
{ rewrite (H234 2 ltac:(tauto)), (su_getr_z (x_regs rsegs cx) (2%bv : bv 5) 2 eq_refl). exact Hsp2. }
assert (A3 : getr regs2 (Z_to_bv 5 3) = w64 (as_gp B)).
{ rewrite (H234 3 ltac:(tauto)), (su_getr_z (x_regs rsegs cx) (3%bv : bv 5) 3 eq_refl). exact Hsgp. }
assert (A4 : getr regs2 (Z_to_bv 5 4) = w64 (as_tp B)).
{ rewrite (H234 4 ltac:(tauto)), (su_getr_z (x_regs rsegs cx) (4%bv : bv 5) 4 eq_refl). exact Hstp. }
pose proof (Hall (LReg 9, e_R (x_e rsegs cx)) ltac:(su_in)) as A9. unfold hd_at in A9; cbn [fst snd] in A9.
pose proof (Hall (LReg 19, shadow_addr (e_F (x_e rsegs cx))) ltac:(su_in)) as A19. unfold hd_at in A19; cbn [fst snd] in A19.
pose proof (Hall (LReg 27, SHADOW_OFF) ltac:(su_in)) as A27. unfold hd_at in A27; cbn [fst snd] in A27.
pose proof (Hall (LReg 21, e_F (x_e rsegs cx)) ltac:(su_in)) as A21. unfold hd_at in A21; cbn [fst snd] in A21.
pose proof (Hall (LReg 23, 1 - e_null (x_e rsegs cx)) ltac:(su_in)) as A23. unfold hd_at in A23; cbn [fst snd] in A23.
pose proof (Hall (LCell XR 0x8, e_pp (x_e rsegs cx) + Layout.OFF_IS_PROPS) ltac:(su_in)) as C8.
pose proof (Hall (LCell XR 0xe0, Z.shiftr (e_pp (x_e rsegs cx) + Layout.OFF_N_ENT) 3) ltac:(su_in)) as CE0.
pose proof (Hall (LCell XR 0x108, - 16381) ltac:(su_in)) as C108.
pose proof (Hall (LCell XR 0x120, e_pp (x_e rsegs cx) + Layout.OFF_N_ENT) ltac:(su_in)) as C120.
pose proof (Hall (LCell XR 0x148, e_pp (x_e rsegs cx)) ltac:(su_in)) as C148.
unfold hd_at, hd_xv in C8, CE0, C108, C120, C148; cbn [fst snd] in C8, CE0, C108, C120, C148.
assert (HFA : frame_addr ly2 4 (x_pos rsegs cx) = e_F (x_e rsegs cx)).
{ rewrite HFdef. exact (su_frame_addr_le _ (x_ly rsegs cx) ly2 (x_lyc rsegs cx) 4 (x_pos rsegs cx)
    (proj1 (proj2 HJ)) (proj1 (proj2 HJ0))). }
unfold HQU_X.
(* ---- the geometry of the frame, the real frame and the shadow row ---- *)
pose proof HJ as (HAR & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
assert (HfinF : In (4, x_pos rsegs cx) (frames S2))
  by (rewrite Hfrs; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HJ0)))))); 
      apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 (x_pos rsegs cx) HAR HfinF) as (HF32 & HFapp & HFb & HFsh).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos rsegs cx) HAR HfinF) as (HF4096 & HFc & _).
rewrite HFA in HF32, HFapp, HFb, HFsh, HF4096, HFc.
change (fs_frame_bytes 4) with 1024 in HFapp, HFb, HFsh, HFc.
change (1024 / 8) with 128 in HFsh.
pose proof (@ASAN_CEIL_range rc) as Hceil. unfold ASAN_CEIL in Hceil.
unfold T_SEG_STK, ASTACK in HRstk.
assert (HRc : alloc_ceiling + 16384 <= e_R (x_e rsegs cx)) by lia.
assert (HFR : e_F (x_e rsegs cx) + 1024 <= e_R (x_e rsegs cx)) by lia.
assert (HshA : 0 <= shadow_addr (e_F (x_e rsegs cx)) /\ shadow_addr (e_F (x_e rsegs cx)) + 128 <= 2 ^ 64)
  by (unfold shadow_addr, SHADOW_OFF; split; lia).
assert (HshR : shadow_addr (e_F (x_e rsegs cx)) + 128 <= e_R (x_e rsegs cx) - 4096)
  by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (HshNA : forall i lo len, 0 <= i < 128 -> in_app lo len ->
  ~ (lo <= shadow_addr (e_F (x_e rsegs cx)) + i < lo + len)).
{ intros i lo len Hi Hap.
  replace (shadow_addr (e_F (x_e rsegs cx)) + i) with (shadow_of_addr SHADOW_OFF (e_F (x_e rsegs cx) + 8 * i))
    by (unfold shadow_of_addr, shadow_addr;
        rewrite (Z.div_mod (e_F (x_e rsegs cx)) 8) at 2 by lia;
        replace (e_F (x_e rsegs cx) mod 8) with 0 by lia;
        rewrite Z.add_0_r, Z.mul_comm, Z.div_add by lia; lia).
  apply (hm_shadow_not_app (e_F (x_e rsegs cx) + 8 * i) lo len); [unfold kHighMemEnd; lia | exact Hap]. }
assert (HshRom : forall i, 0 <= i < 128 -> ~ in_rom rsegs (shadow_addr (e_F (x_e rsegs cx)) + i)).
{ intros i Hi Hro'. destruct Hro' as (sg & Hsg & _ & Hr).
  assert (Hin : in_img rsegs (shadow_addr (e_F (x_e rsegs cx)) + i)) by (exists sg; auto).
  pose proof (Hsegs _ Hin) as Hlow.
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia. }
assert (HFnoimg : forall a, e_F (x_e rsegs cx) <= a < e_F (x_e rsegs cx) + 1024 -> ~ in_rom rsegs a).
{ intros a Ha Hro'.
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR
    ltac:(right; left; exists 4, (x_pos rsegs cx); split; [exact HfinF|];
          rewrite HFA; change (fs_frame_bytes 4) with 1024; lia)) as (_ & Hni).
  apply Hni. destruct Hro' as (sg & Hsg & _ & Hr). exists sg. auto. }
eapply (@su_A fx2 rc SK B MT MTL AMEMSET).
- exact HJ.
- exact Hown.
- exact HFA.
- exact A2.
- exact A3.
- exact A4.
- exact A19.
- exact A21.
- exact HR32.
- rewrite <- HeS. exact HRsz.
- exact HRstk.
- intros ly1 S1 W1 regsA memA mdA HA.
  destruct HA as (HJA & HfrA & HpmA & HioA & HmoA & HlyA & HkA & HA18 & Hxz & HshZ & HkeepA & HgrA).
  pose proof HJA as (HAR1 & _).
  assert (HPP : In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly1 S1)).
  { apply (Permutation_in _ (Permutation_sym HpmA)).
    apply (Permutation_in _ (Permutation_sym Hperm)). exact (proj1 (proj2 Hppf)). }
  change Layout.PP_SIZE with 19744 in HPP.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_pp (x_e rsegs cx)) 19744 HAR1 HPP)
    as (Hp16 & Hp4096 & Hpc & Happ & Hpb & _).
  change (req_size 19744) with 19744 in Hpc, Happ, Hpb.
  assert (HfinF1 : In (4, x_pos rsegs cx) (frames S1)) by (rewrite HfrA; exact HfinF).
  pose proof (sep_block_frame rsegs B LAWS ly1 S1 W1 memA mdA (e_pp (x_e rsegs cx)) 19744 4 (x_pos rsegs cx)
    HAR1 HPP HfinF1) as Hbdis.
  change (req_size 19744) with 19744 in Hbdis.
  change (fs_frame_bytes 4) with 1024 in Hbdis.
  assert (HFA1 : frame_addr ly1 4 (x_pos rsegs cx) = e_F (x_e rsegs cx))
    by (rewrite <- HFA; exact (su_frame_addr_le _ (x_ly rsegs cx) ly1 ly2 4 (x_pos rsegs cx) HlyA Hly2)).
  rewrite HFA1 in Hbdis. unfold zdisjoint in Hbdis. cbn [fst snd] in Hbdis.
  (* the registers su_B reads *)
  assert (B9 : getr regsA (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
    by (rewrite (HkA 9 ltac:(cbn [In]; tauto)); exact A9).
  assert (B21 : getr regsA (Z_to_bv 5 21) = w64 (e_F (x_e rsegs cx)))
    by (rewrite (HkA 21 ltac:(cbn [In]; tauto)); exact A21).
  assert (B27 : getr regsA (Z_to_bv 5 27) = w64 SHADOW_OFF)
    by (rewrite (HkA 27 ltac:(cbn [In]; tauto)); exact A27).
  assert (B23 : getr regsA (Z_to_bv 5 23) = w64 (if e_null (x_e rsegs cx) =? 1 then 0 else 1)).
  { rewrite (HkA 23 ltac:(cbn [In]; tauto)), A23. unfold w64. f_equal.
    destruct (Z.eqb_spec (e_null (x_e rsegs cx)) 1); lia. }
  (* the real-frame cells, carried across the memset *)
  assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 4096 <= a < e_R (x_e rsegs cx)) ->
    ~ (e_F (x_e rsegs cx) + 0x2c0 <= a < e_F (x_e rsegs cx) + 0x2c0 + 136) ->
    ~ (shadow_addr (e_F (x_e rsegs cx)) + 88 <= a < shadow_addr (e_F (x_e rsegs cx)) + 105) ->
    aview rsegs (w_H W1) memA a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha H2' H3' H4'.
    apply HkeepA; [lia | unfold ESTACK; lia | unfold SU_XO; lia | lia]. }
  assert (KAr : forall a, e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x160 ->
    aview rsegs (w_H W1) memA a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply KA3; lia. }
  assert (KApp : forall a, e_pp (x_e rsegs cx) <= a < e_pp (x_e rsegs cx) + 19744 ->
    aview rsegs (w_H W1) memA a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply KA3; [lia | lia | lia |].
    intros HH. apply (HshNA (a - shadow_addr (e_F (x_e rsegs cx))) (e_pp (x_e rsegs cx)) 19744 ltac:(lia) Happ). lia. }
  assert (CA8 : val_mem rsegs (mrestrict (w_H W1) memA) (e_R (x_e rsegs cx) + 0x8) 8 (e_pp (x_e rsegs cx) + 0x4008)).
  { rewrite Z.mod_small in C8 by (unfold Layout.OFF_IS_PROPS; lia).
    apply (su_val_kept (w_H W2) (w_H W1) mem2 memA _ _ _ C8).
    intros i Hi. cbn [Z.of_nat] in Hi. apply KAr. lia. }
  assert (CAE0 : val_mem rsegs (mrestrict (w_H W1) memA) (e_R (x_e rsegs cx) + 0xe0) 8
    (Z.shiftr (e_pp (x_e rsegs cx) + 0x4d14) 3)).
  { rewrite Z.mod_small in CE0
      by (rewrite Z.shiftr_div_pow2 by lia; unfold Layout.OFF_N_ENT;
          split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    apply (su_val_kept (w_H W2) (w_H W1) mem2 memA _ _ _ CE0).
    intros i Hi. cbn [Z.of_nat] in Hi. apply KAr. lia. }
  assert (CA108 : val_mem rsegs (mrestrict (w_H W1) memA) (e_R (x_e rsegs cx) + 0x108) 8 ((-16381) mod 2 ^ 64)).
  { apply (su_val_kept (w_H W2) (w_H W1) mem2 memA _ _ _ C108).
    intros i Hi. cbn [Z.of_nat] in Hi. apply KAr. lia. }
  assert (CA120 : val_mem rsegs (mrestrict (w_H W1) memA) (e_R (x_e rsegs cx) + 0x120) 8 (e_pp (x_e rsegs cx) + 0x4d14)).
  { rewrite Z.mod_small in C120 by (unfold Layout.OFF_N_ENT; lia).
    apply (su_val_kept (w_H W2) (w_H W1) mem2 memA _ _ _ C120).
    intros i Hi. cbn [Z.of_nat] in Hi. apply KAr. lia. }
  assert (CA148 : val_mem rsegs (mrestrict (w_H W1) memA) (e_R (x_e rsegs cx) + 0x148) 8 (e_pp (x_e rsegs cx))).
  { rewrite Z.mod_small in C148 by lia.
    apply (su_val_kept (w_H W2) (w_H W1) mem2 memA _ _ _ C148).
    intros i Hi. cbn [Z.of_nat] in Hi. apply KAr. lia. }
  assert (Hb16 : Z.of_nat (length (Model.buf r)) <= Layout.POD_BUF_MAX).
  { destruct Hwf as (_ & _ & _ & _ & H5440 & Hcw). unfold Model.buf.
    unfold Model.corr_wf in Hcw. destruct (Model.p_corr r) as [[off bs]|];
    [|unfold Layout.POD_BUF_MAX; lia].
    unfold Model.overwrite. rewrite !length_app, length_firstn, length_skipn.
    unfold Layout.POD_BUF_MAX in *. lia. }
  assert (Hents : Forall Model.ent_wf (Model.ents r) /\ (length (Model.ents r) <= 32)%nat).
  { destruct Hwf as (_ & Hps & Hallw & _ & _ & _). unfold Model.ents, Model.first_params.
    destruct (find (fun kv => fst kv =? Model.POD_PROP_PARAMS) (Model.p_props r)) as [kv|] eqn:Ef;
    [|cbn [option_map]; split; [apply Forall_nil | cbn [length]; lia]].
    cbn [option_map]. destruct (snd kv) as [v|es] eqn:Ev;
    [split; [apply Forall_nil | cbn [length]; lia]|].
    apply find_some in Ef as [Hin _].
    rewrite Forall_forall in Hps. destruct (Hps kv Hin) as (_ & Hpv). rewrite Ev in Hpv.
    cbn [Model.pval_wf] in Hpv. split; [|exact Hpv].
    rewrite Forall_forall in Hallw |- *. intros xx Hx. apply Hallw.
    unfold Model.all_ents. apply in_flat_map. exists kv. split; [exact Hin|]. rewrite Ev. exact Hx. }
  assert (Hbody : Forall (fun en => (length (Model.e_body en) <= 96)%nat) (Model.ents r)).
  { eapply Forall_impl; [|exact (proj1 Hents)]. intros en (_ & Hl & Hz). lia. }
  assert (HppLen : Z.of_nat (length (hd_zbytes (Layout.pp_bytes r))) = 19744).
  { unfold hd_zbytes. rewrite length_map.
    exact (Layout.length_pp_image (Model.buf r) (Model.is_props r) (Model.has_params r)
      (Model.params_struct r) (Model.ents r) (Model.corrupt r) Hb16 (proj2 Hents) Hbody). }
  assert (HppA : hm_bytes rsegs (w_H W1) memA (e_pp (x_e rsegs cx)) (Layout.pp_bytes r)).
  { apply (su_garr8_kept (w_H W2) (w_H W1) mem2 memA _ _ Hppat).
    intros i Hi. rewrite HppLen in Hi. apply KApp. lia. }
  assert (Vip : val_mem rsegs (mrestrict (w_H W1) memA) (e_pp (x_e rsegs cx) + 0x4008)
    4 (Z.b2z (Model.is_props r)))
    by (exact (hm_pp_is_props rsegs (Model.buf r) (Model.is_props r) (Model.has_params r)
         (Model.params_struct r) (Model.ents r) (Model.corrupt r) Hb16 (proj2 Hents) Hbody
         (w_H W1) memA (e_pp (x_e rsegs cx)) HppA)).
  assert (Vps : val_mem rsegs (mrestrict (w_H W1) memA) (e_pp (x_e rsegs cx) + 0x4010)
    4 (Z.b2z (Model.params_struct r)))
    by (exact (hm_pp_params_struct rsegs (Model.buf r) (Model.is_props r) (Model.has_params r)
         (Model.params_struct r) (Model.ents r) (Model.corrupt r) Hb16 (proj2 Hents) Hbody
         (w_H W1) memA (e_pp (x_e rsegs cx)) HppA)).
  assert (Vn : val_mem rsegs (mrestrict (w_H W1) memA) (e_pp (x_e rsegs cx) + 0x4d14)
    4 (Z.of_nat (length (Model.ents r))))
    by (exact (hm_pp_n_ent rsegs (Model.buf r) (Model.is_props r) (Model.has_params r)
         (Model.params_struct r) (Model.ents r) (Model.corrupt r) Hb16 (proj2 Hents) Hbody
         (w_H W1) memA (e_pp (x_e rsegs cx)) HppA)).
  (* ---- the written set avoids the first block, the pod, the out block, res and the image ---- *)
  assert (HspR : spZ (x_regs rsegs cx) = e_R (x_e rsegs cx)).
  { unfold spZ. rewrite Hsp2. unfold w64. apply unsigned_lit_small. lia. }
  assert (HWRblk : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
    ~ su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a).
  { intros p n a Hin Ha HH.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR1 Hin) as (_ & Hp0 & Hpc' & Happ' & _).
    pose proof (sep_block_frame rsegs B LAWS ly1 S1 W1 memA mdA p n 4 (x_pos rsegs cx)
      HAR1 Hin HfinF1) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFA1 in Hd.
    change (fs_frame_bytes 4) with 1024 in Hd.
    unfold su_WR, ESTACK, SU_XO in HH.
    destruct HH as [HH|[HH|[HH|HH]]]; [lia | lia | | lia].
    apply (HshNA (a - shadow_addr (e_F (x_e rsegs cx))) p (req_size n) ltac:(lia) Happ'). lia. }
  assert (HWRres : forall a, e_F (x_e rsegs cx) + 0x2a0 <= a < e_F (x_e rsegs cx) + 0x2ac ->
    ~ su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a).
  { intros a Ha HH. unfold su_WR, ESTACK, SU_XO in HH.
    destruct HH as [HH|[HH|[HH|HH]]]; [lia | lia | | lia].
    apply (HshNA (a - shadow_addr (e_F (x_e rsegs cx))) (e_F (x_e rsegs cx) + 0x2a0) 12
      ltac:(lia) ltac:(apply (in_app_sub (e_F (x_e rsegs cx)) 1024); [exact HFapp | lia | lia | lia])).
    lia. }
  assert (HWRrom : forall a, in_rom rsegs a -> ~ su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a).
  { intros a Hro' HH.
    assert (Hlow : a < kLowMemEnd).
    { destruct Hro' as (sg & Hsg & _ & Hr). apply Hsegs. exists sg. auto. }
    unfold su_WR, ESTACK, SU_XO in HH.
    destruct HH as [HH|[HH|[HH|HH]]]; [unfold kLowMemEnd in Hlow; lia | | | ].
    - exact (HFnoimg a ltac:(lia) Hro').
    - exact (HshRom (a - shadow_addr (e_F (x_e rsegs cx))) ltac:(lia)
        ltac:(replace (shadow_addr (e_F (x_e rsegs cx)) + (a - shadow_addr (e_F (x_e rsegs cx))))
              with a by ring; exact Hro')).
    - unfold kLowMemEnd in Hlow. lia. }
  assert (HWRsh : forall i, 0 <= i < 128 -> ~ (88 <= i < 105) ->
    ~ su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (shadow_addr (e_F (x_e rsegs cx)) + i)).
  { intros i Hi Hni HH. unfold su_WR, ESTACK, SU_XO in HH.
    destruct HH as [HH|[HH|[HH|HH]]]; [lia | | lia | lia].
    apply (HshNA i (e_F (x_e rsegs cx) + 0x2c0) 136 Hi
      ltac:(apply (in_app_sub (e_F (x_e rsegs cx)) 1024); [exact HFapp | lia | lia | lia])). lia. }
  assert (HWRE3 : forall a, su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a ->
    (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) \/ hqu_E3 rsegs B cx a).
  { intros a HH. rewrite HspR. unfold T_SEG_STK, ASTACK.
    unfold su_WR, ESTACK, SU_XO in HH. unfold hqu_E3, hd_inw.
    cbn [hi_w3 headamp_himg_B].
    destruct HH as [HH|[HH|[HH|HH]]]; [left; lia | right; left | right; left | right; left].
    - apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
    - apply Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
    - apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
  (* the three blocks of the run, live at the current state *)
  assert (HPOD : In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B ly1 S1)).
  { apply (Permutation_in _ (Permutation_sym HpmA)).
    apply (Permutation_in _ (Permutation_sym Hperm)). exact (proj1 (proj2 Hpodf)). }
  assert (HOUT : In (e_out (x_e rsegs cx), 3 * (e_cap (x_e rsegs cx) + 1)) (ablocks B ly1 S1)).
  { apply (Permutation_in _ (Permutation_sym HpmA)).
    apply (Permutation_in _ (Permutation_sym Hperm)). exact (proj1 (proj2 Houtf)). }
  assert (EXIT : forall (fx3 : YK11.FPState) regs3 mem3 md3,
    ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
      (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
      ly1 S1 W1 mem3 md3 (x_k rsegs cx) ->
    same_io mdA md3 -> su_B_keep (e_R (x_e rsegs cx)) W1 memA mem3 -> su_B_kept regsA regs3 ->
    hd_fxk HQU_FXK fx fx3 ->
    @hqu_base3 fx rc SK rsegs B MT cx fx3 r hqu_shX ly1 S1 W1 regs3 mem3 md3 /\
    (forall off v, (0 <= off /\ off + 8 <= 0x98) \/ (0x140 <= off /\ off + 8 <= 0x160) ->
     hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR off) v ->
     hd_at rsegs (w_H W1) mem3 regs3 (x_e rsegs cx) (LCell XR off) v) /\
    (forall r0 v, In r0 [2; 3; 4; 8; 9; 19; 20; 22; 25; 26; 27] ->
     hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LReg r0) v ->
     hd_at rsegs (w_H W1) mem3 regs3 (x_e rsegs cx) (LReg r0) v) /\
    (forall cs keys rf, cs = [] -> keys = 0 -> rf = Headamp.REFUSE_NONE ->
     hqu_x_at rsegs cx W1 mem3 cs keys rf)).
  { intros fx3 regs3 mem3 md3 HJ3 Hio3 HK3 Hkept3 Hfxk3.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a ->
      aview rsegs (w_H W1) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha Hn. unfold su_WR in Hn.
      rewrite (proj1 HK3 a Ha ltac:(tauto)).
      apply HkeepA; [lia | unfold ESTACK; tauto | tauto | tauto]. }
    assert (GROW : forall a, 0 <= a < 2 ^ 64 ->
      aview rsegs (w_H W2) mem2 a <> None -> aview rsegs (w_H W1) mem3 a <> None)
      by (intros a Ha Hv; apply (proj2 HK3); apply HgrA; assumption).
    assert (BASE3 : @hqu_base3 fx rc SK rsegs B MT cx fx3 r hqu_shX ly1 S1 W1 regs3 mem3 md3).
    { split.
      { split; [exact HJ3|].
        split.
        { intros r0 Hr0. rewrite (Hkept3 r0 ltac:(cbn [In]; lia)).
          rewrite (HkA r0 ltac:(cbn [In]; lia)). exact (H234 r0 Hr0). }
        split; [rewrite HfrA; exact Hfrs|].
        split; [exact (Permutation_trans HpmA Hperm)|].
        split; [eapply same_io_trans; [exact Hio|];
                eapply same_io_trans; [exact HioA | exact Hio3]|].
        split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo HmoA)|].
        intros a Ha Hstk' HE3. rewrite (KEEP a Ha ltac:(intros HH; destruct (HWRE3 a HH); tauto)).
        apply Hkeep; assumption. }
      split; [exact Hfxk3|].
      split.
      { unfold hsu_fsh_at. rewrite <- su_shX_set.
        apply (hm_fsh_set rsegs (w_H W2) mem2 (w_H W1) mem3 (e_F (x_e rsegs cx)) headamp_B_shB 88 17 0).
        - exact Hfsh.
        - intros i Hi. rewrite (proj1 HK3) by (unfold ESTACK in *; lia). apply HshZ. lia.
        - intros i Hi Hni. rewrite hqu_shB_len in Hi.
          apply KEEP; [unfold shadow_addr, SHADOW_OFF in *; lia | apply HWRsh; lia]. }
      split.
      { apply (hm_rom_kept_wr rsegs
          (fun a => ~ (0 <= a < 2 ^ 64) \/ su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a)
          W2 W1 mem2 mem3 Hrom).
        - intros a Hn. apply KEEP; [|intros HH; apply Hn; right; exact HH].
          destruct (Z.le_gt_cases 0 a) as [H0|H0]; [destruct (Z.lt_ge_cases a (2 ^ 64)) as [H1|H1]|];
          [lia | exfalso; apply Hn; left; lia | exfalso; apply Hn; left; lia].
        - intros a Hro' [HH|HH]; [|exact (HWRrom a Hro' HH)].
          apply HH. destruct Hro' as (sg & Hsg & Hsw & Hr).
          pose proof (Hsegs a ltac:(exists sg; auto)) as Hl. unfold kLowMemEnd in Hl. lia. }
      split.
      { unfold hsu_pp_at. apply (su_garr8_kept (w_H W2) (w_H W1) mem2 mem3 _ _ Hppat).
        intros i Hi. rewrite HppLen in Hi.
        apply KEEP; [lia | apply (HWRblk (e_pp (x_e rsegs cx)) 19744);
          [exact HPP | change (req_size 19744) with 19744; lia]]. }
      split.
      { apply (su_garr8_kept (w_H W2) (w_H W1) mem2 mem3 _ _ Hpodat).
        intros i Hi. unfold hd_zbytes in Hi. rewrite length_map in Hi.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_pod (x_e rsegs cx)) (e_len (x_e rsegs cx))
          HAR1 HPOD) as (_ & Hd0 & Hdc & _ & _).
        apply KEEP; [pose proof (req_size_pos (e_len (x_e rsegs cx)) ltac:(lia)); lia |].
        apply (HWRblk (e_pod (x_e rsegs cx)) (e_len (x_e rsegs cx))); [exact HPOD|].
        pose proof (req_size_pos (e_len (x_e rsegs cx)) ltac:(lia)). lia. }
      split.
      { apply (su_garr8_kept (w_H W2) (w_H W1) mem2 mem3 _ _ Houtat).
        intros i Hi. unfold hd_zbytes in Hi. rewrite length_map in Hi.
        rewrite length_ha_cells_bytes in Hi.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_out (x_e rsegs cx))
          (3 * (e_cap (x_e rsegs cx) + 1)) HAR1 HOUT) as (_ & Ho0 & Hoc & _ & _).
        pose proof (req_size_pos (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)) as Hrq.
        destruct (proj1 (answer_ok_parts (e_cap (x_e rsegs cx)) (hqu_ans rsegs cx r)
          (Headamp.parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r))
             (e_cap (x_e rsegs cx)) ltac:(lia)))) as [Hz|Hz].
        - rewrite (proj1 (proj2 Hz)) in Hi. cbn [length] in Hi.
          apply KEEP; [lia | apply (HWRblk (e_out (x_e rsegs cx)) (3 * (e_cap (x_e rsegs cx) + 1)));
            [exact HOUT | lia]].
        - apply KEEP; [lia | apply (HWRblk (e_out (x_e rsegs cx)) (3 * (e_cap (x_e rsegs cx) + 1)));
            [exact HOUT | lia]]. }
      split.
      { apply (su_garr8_kept (w_H W2) (w_H W1) mem2 mem3 _ _ Hresat).
        intros i Hi. unfold hd_zbytes in Hi. rewrite length_map in Hi. unfold ans_res_bytes in Hi. rewrite length_ha_res_bytes in Hi.
        change HQU_RES with 0x2a0.
        apply KEEP; [lia | apply HWRres; lia]. }
      assert (GROWa : forall a, aview rsegs (w_H W2) mem2 a <> None ->
        aview rsegs (w_H W1) mem3 a <> None).
      { intros a Hv. rewrite su_aview_wrap. rewrite su_aview_wrap in Hv.
        apply GROW; [apply Z.mod_pos_bound; lia | exact Hv]. }
      destruct Hev as (ev2 & Hev2).
      destruct (su_rd32_grows (w_H W2) (w_H W1) mem2 mem3 (as_errno B) ev2 Hev2 GROWa)
        as (ev3 & Hev3).
      exists ev3. exact Hev3. }
    assert (KEEPW : forall a, ~ (~ (0 <= a < 2 ^ 64) \/
      su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a) ->
      aview rsegs (w_H W1) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Hn. apply KEEP; [|intros HH; apply Hn; right; exact HH].
      destruct (Z.le_gt_cases 0 a) as [H0|H0];
      [destruct (Z.lt_ge_cases a (2 ^ 64)) as [H1|H1]; [lia|] | ]; exfalso; apply Hn; left; lia. }
    assert (CELLR : forall off v, (0 <= off /\ off + 8 <= 0x98) \/ (0x140 <= off /\ off + 8 <= 0x160) ->
      hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR off) v ->
      hd_at rsegs (w_H W1) mem3 regs3 (x_e rsegs cx) (LCell XR off) v).
    { intros off v Hoff Hv.
      apply (hm_at_kept rsegs (w_H W2) mem2 (w_H W1) mem3 regs2 regs3 (x_e rsegs cx)
        (LCell XR off) v Hv).
      apply (hm_keeps_of rsegs (fun a => ~ (0 <= a < 2 ^ 64) \/
        su_WR (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a)
        (w_H W2) mem2 (w_H W1) mem3 regs2 regs3 (x_e rsegs cx) (LCell XR off) KEEPW).
      cbn [hd_xv]. intros i Hi [HH|HH];
      [apply HH; lia | unfold su_WR, ESTACK, SU_XO in HH; lia]. }
    assert (REGK : forall r0 v, In r0 [2; 3; 4; 8; 9; 19; 20; 22; 25; 26; 27] ->
      hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LReg r0) v ->
      hd_at rsegs (w_H W1) mem3 regs3 (x_e rsegs cx) (LReg r0) v).
    { intros r0 v Hin Hv. unfold hd_at in Hv |- *.
      rewrite (Hkept3 r0 Hin), (HkA r0 ltac:(cbn [In] in Hin |- *; tauto)). exact Hv. }
    assert (HXZ : forall i, 0 <= i < 136 ->
      aview rsegs (w_H W1) mem3 (e_F (x_e rsegs cx) + 0x2c0 + i) = Some 0).
    { intros i Hi. rewrite (proj1 HK3) by (unfold ESTACK in *; lia).
      change 0x2c0 with SU_XO. apply Hxz. lia. }
    assert (HXAT : forall cs keys rf, cs = [] -> keys = 0 -> rf = Headamp.REFUSE_NONE ->
      hqu_x_at rsegs cx W1 mem3 cs keys rf).
    { intros cs keys rf -> -> ->. unfold hqu_x_at. split.
      { rewrite su_x_zero. intros j Hj. rewrite repeat_length in Hj.
        rewrite nth_repeat.
        destruct (hm_aview_val1 rsegs (w_H W1) mem3 (e_F (x_e rsegs cx) + HQU_XO + Z.of_nat j) 0
          ltac:(change HQU_XO with 0x2c0; apply HXZ; lia)) as (Hv & Hb).
        split; [exact Hv | lia]. }
      split; [cbn [length]; unfold X_CELLS; lia|].
      split; [cbn [length]; lia|].
      split; [cbn [length]; lia|].
      split; [lia | left; reflexivity]. }
    split; [exact BASE3|]. split; [exact CELLR|]. split; [exact REGK | exact HXAT]. }
  apply (@su_B fx2 rc SK B MT MTL (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly1 S1 W1
    memA mdA (x_k rsegs cx) regsA (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (e_pp (x_e rsegs cx)) (e_null (x_e rsegs cx) =? 1) (Model.is_props r)
    (Model.params_struct r) POST).
  + exact HJA.
  + exact HPP.
  + exact B9.
  + exact HA18.
  + exact B21.
  + exact B23.
  + exact B27.
  + exact HR32.
  + rewrite <- HeS. exact HRsz.
  + exact HRstk.
  + lia.
  + lia.
  + exact CA8.
  + exact CAE0.
  + exact CA108.
  + exact CA120.
  + exact CA148.
  + exact Vip.
  + exact Vps.
  + (* ---- RCM 0x8385c: the null flag, or not an Object of Props ---- *)
    intros regs3 mem3 md3 HBp H13 H18' H21' Hcase.
    destruct HBp as (HJ3 & Hio3 & HK3 & Hkept3).
    destruct (EXIT fx2 regs3 mem3 md3 HJ3 Hio3 HK3 Hkept3 Hfxk)
      as (BASE3 & CELLR & REGK & HXAT).
    (* ---- the cut at RCM ---- *)
    assert (Hexp : hqu_exp rsegs cx r = (-1, [], (0, 0, Headamp.REFUSE_NONE))).
    { unfold hqu_exp. apply su_exp_m1.
      destruct Hcase as [Hc|Hc]; [left; rewrite Hc; reflexivity | right; exact Hc]. }
    apply (HRCM fx2 ly1 S1 W1 regs3 mem3 md3).
    split; [exact BASE3|].
    split.
    { unfold hsu_at_cx, hsu_at, hqu_L_seg, hqu_L_frame. rewrite <- !app_assoc. cbn [app].
      repeat apply Forall_cons; cbv beta; cbn [fst snd].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 8, e_S (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 9, e_R (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto |
          apply (Hall (LReg 19, shadow_addr (e_F (x_e rsegs cx)))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 27, SHADOW_OFF)); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 20, e_cap (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 22, e_out (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 25, e_rc (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto |
          apply (Hall (LReg 26, e_F (x_e rsegs cx) + HQU_RES)); su_in].
      - unfold hd_at. rewrite Hexp. cbn [ans_rc fst snd]. exact H13.
      - unfold hd_at. rewrite H18'. exact HA18.
      - unfold hd_at. rewrite H21'. exact B21.
      - apply CELLR; [lia | apply (Hall (LCell XR 0x18, e_F (x_e rsegs cx))); su_in].
      - apply CELLR; [lia | apply (Hall (LCell XR 0x48, e_F (x_e rsegs cx))); su_in].
      - apply CELLR; [lia |
          apply (Hall (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps)); su_in].
      - apply CELLR; [lia | apply (Hall (LCell XR 0x148, e_pp (x_e rsegs cx))); su_in].
      - apply CELLR; [lia |
          apply (Hall (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3)); su_in].
      - apply CELLR; [lia | apply (Hall (LCell XR 0x158, e_pod (x_e rsegs cx))); su_in].
      - apply Forall_nil. }
    split; [exact Hcorr|].
    rewrite Hexp. cbn [ans_cells ans_keys ans_rf fst snd]. apply HXAT; reflexivity.
  + (* ---- RC 0x83850: the params property is not a Struct ---- *)
    intros regs3 mem3 md3 HBp V138 Hnl Hip Hps.
    destruct HBp as (HJ3 & Hio3 & HK3 & Hkept3).
    destruct (EXIT fx2 regs3 mem3 md3 HJ3 Hio3 HK3 Hkept3 Hfxk)
      as (BASE3 & CELLR & REGK & HXAT).
    assert (Hexp : hqu_exp rsegs cx r = (0, [], (0, 0, Headamp.REFUSE_NONE))).
    { unfold hqu_exp. rewrite Hnl. apply su_exp_0; [exact Hip | exact Hps]. }
    apply (HRC fx2 ly1 S1 W1 regs3 mem3 md3).
    split; [exact BASE3|].
    split.
    { unfold hsu_at_cx, hsu_at, hqu_L_seg, hqu_L_frame. rewrite <- !app_assoc. cbn [app].
      repeat apply Forall_cons; cbv beta; cbn [fst snd].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 8, e_S (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 9, e_R (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto |
          apply (Hall (LReg 19, shadow_addr (e_F (x_e rsegs cx)))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 27, SHADOW_OFF)); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 20, e_cap (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 22, e_out (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 25, e_rc (x_e rsegs cx))); su_in].
      - apply REGK; [cbn [In]; tauto |
          apply (Hall (LReg 26, e_F (x_e rsegs cx) + HQU_RES)); su_in].
      - apply CELLR; [lia | apply (Hall (LCell XR 0x18, e_F (x_e rsegs cx))); su_in].
      - apply CELLR; [lia | apply (Hall (LCell XR 0x48, e_F (x_e rsegs cx))); su_in].
      - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_XO; lia). exact V138.
      - apply CELLR; [lia |
          apply (Hall (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps)); su_in].
      - apply CELLR; [lia | apply (Hall (LCell XR 0x148, e_pp (x_e rsegs cx))); su_in].
      - apply CELLR; [lia |
          apply (Hall (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3)); su_in].
      - apply CELLR; [lia | apply (Hall (LCell XR 0x158, e_pod (x_e rsegs cx))); su_in].
      - apply Forall_nil. }
    split; [exact Hcorr|].
    rewrite Hexp. cbn [ans_rc ans_cells ans_keys ans_rf fst snd length].
    split; [reflexivity | apply HXAT; reflexivity].
  + (* ---- PAIR 0x8314c, or, when the record has no entry, on through the pair head to RC ---- *)
    intros regs3 mem3 md3 HBp HCS Hregs Hnl Hip Hps.
    destruct HBp as (HJ3 & Hio3 & HK3 & Hkept3).
    destruct HCS as (K98 & KA0 & KA8 & KB0 & KB8 & KC0 & KC8 & KD0 & K118 & K120 & K128 & K130 & K138).
    destruct Hregs as (G5 & G6 & G7 & G12 & G21 & G28 & G29 & G30 & G31).
    assert (HFXK3 : hd_fxk HQU_FXK fx (su_fx3 fx2)).
    { destruct Hfxk as (Hk1 & Hk2). split.
      - intros kk Hkk.
        assert (N9 : kk <> Z_to_bv 5 9) by (intros HH; apply Hkk; rewrite HH; cbn; tauto).
        assert (N18 : kk <> Z_to_bv 5 18) by (intros HH; apply Hkk; rewrite HH; cbn; tauto).
        assert (N19 : kk <> Z_to_bv 5 19) by (intros HH; apply Hkk; rewrite HH; cbn; tauto).
        unfold su_fx3, su_fset. cbn [fp_regs]. unfold reg_get.
        rewrite !bvmap_get_set_other by congruence. apply Hk1. exact Hkk.
      - unfold su_fx3, su_fset. cbn [fp_csr]. exact Hk2. }
    destruct (EXIT (su_fx3 fx2) regs3 mem3 md3 HJ3 Hio3 HK3 Hkept3 HFXK3)
      as (BASE3 & CELLR & REGK & HXAT).
    assert (Hnull0 : e_null (x_e rsegs cx) = 0)
      by (destruct (Z.eqb_spec (e_null (x_e rsegs cx)) 1) as [Hq|Hq]; [discriminate Hnl | lia]).
    assert (Hlive : hqu_live rsegs cx r).
    { unfold hqu_live. split; [exact Hnull0|]. split; [exact Hcorr|]. split; assumption. }
    assert (HFS : hqu_fs (su_fx3 fx2) 9 HQU_F32_M1 /\ hqu_fs (su_fx3 fx2) 18 HQU_F32_256 /\
      hqu_fs (su_fx3 fx2) 19 HQU_F32_2P63).
    { unfold hqu_fs, su_fx3, su_fset. cbn [fp_regs]. unfold reg_get.
      split; [|split].
      - rewrite bvmap_get_set_other
          by (intros HH; apply (f_equal (@bv_unsigned 5)) in HH; vm_compute in HH; discriminate HH).
        rewrite bvmap_get_set_other
          by (intros HH; apply (f_equal (@bv_unsigned 5)) in HH; vm_compute in HH; discriminate HH).
        rewrite bvmap_get_set_same. reflexivity.
      - rewrite bvmap_get_set_other
          by (intros HH; apply (f_equal (@bv_unsigned 5)) in HH; vm_compute in HH; discriminate HH).
        rewrite bvmap_get_set_same. reflexivity.
      - rewrite bvmap_get_set_same. reflexivity. }
    assert (Hfold : hqu_fold_inv rsegs cx r 0 [] 0 Headamp.REFUSE_NONE).
    { unfold hqu_fold_inv, hqu_fin, hqu_exp, Headamp.expect_model.
      change (skipn 0 (Model.ents r)) with (Model.ents r).
      rewrite Hnl, Hip, Hps. cbn [negb orb]. unfold Accessors.pairs.
      destruct (Headamp.ha_fold Headamp.expect_cell (e_cap (x_e rsegs cx))
        (Accessors.pairs_by Accessors.key_of (Model.ents r) None) [] 0 Headamp.REFUSE_NONE)
        as ((cs0 & ks0) & rf0) eqn:Eo.
      unfold Headamp.ha_result, ans_cells, ans_keys, ans_rf. cbn [fst snd]. reflexivity. }
    destruct (Z.eq_dec (hqu_nent r) 0) as [Hn0|Hn0].
    * (* no entry at all: the pair head's five instructions reach RC *)
      assert (Hents0 : Model.ents r = []).
      { unfold hqu_nent in Hn0. destruct (Model.ents r) as [|a0 l0]; [reflexivity|].
        cbn [length] in Hn0. lia. }
      assert (Vn3 : val_mem rsegs (mrestrict (w_H W1) mem3) (e_pp (x_e rsegs cx) + 0x4d14) 4 0).
      { rewrite Hents0 in Vn. cbn [length Z.of_nat] in Vn.
        apply (su_val_kept (w_H W1) (w_H W1) memA mem3 _ _ _ Vn).
        intros i Hi. apply (proj1 HK3); lia. }
      apply (@su_N0 (su_fx3 fx2) rc SK B MT MTL (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
        (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
        ly1 S1 W1 mem3 md3 (x_k rsegs cx) regs3 (e_R (x_e rsegs cx)) (e_pp (x_e rsegs cx)) POST
        HJ3 HPP ltac:(rewrite (Hkept3 9 ltac:(cbn [In]; tauto)); exact B9) G12
        ltac:(rewrite (Hkept3 27 ltac:(cbn [In]; tauto)); exact B27)
        ltac:(rewrite <- HeS; exact HRsz) HRstk K120 K130 Vn3).
      intros regs4 md4 HJ4 Hio4 Hk4.
      assert (Hkept4 : su_B_kept regsA regs4).
      { intros r0 Hr0. rewrite (Hk4 r0 ltac:(cbn [In] in Hr0 |- *; tauto)).
        apply Hkept3. exact Hr0. }
      destruct (EXIT (su_fx3 fx2) regs4 mem3 md4 HJ4
        ltac:(eapply same_io_trans; [exact Hio3 | exact Hio4]) HK3 Hkept4 HFXK3)
        as (BASE4 & CELLR4 & REGK4 & HXAT4).
      assert (Hexp : hqu_exp rsegs cx r = (0, [], (0, 0, Headamp.REFUSE_NONE))).
      { unfold hqu_exp. rewrite Hnl. apply su_exp_nil; assumption. }
      apply (HRC (su_fx3 fx2) ly1 S1 W1 regs4 mem3 md4).
      split; [exact BASE4|].
      split.
      { unfold hsu_at_cx, hsu_at, hqu_L_seg, hqu_L_frame. rewrite <- !app_assoc. cbn [app].
        repeat apply Forall_cons; cbv beta; cbn [fst snd].
        - apply REGK4; [cbn [In]; tauto | apply (Hall (LReg 8, e_S (x_e rsegs cx))); su_in].
        - apply REGK4; [cbn [In]; tauto | apply (Hall (LReg 9, e_R (x_e rsegs cx))); su_in].
        - apply REGK4; [cbn [In]; tauto |
            apply (Hall (LReg 19, shadow_addr (e_F (x_e rsegs cx)))); su_in].
        - apply REGK4; [cbn [In]; tauto | apply (Hall (LReg 27, SHADOW_OFF)); su_in].
        - apply REGK4; [cbn [In]; tauto | apply (Hall (LReg 20, e_cap (x_e rsegs cx))); su_in].
        - apply REGK4; [cbn [In]; tauto | apply (Hall (LReg 22, e_out (x_e rsegs cx))); su_in].
        - apply REGK4; [cbn [In]; tauto | apply (Hall (LReg 25, e_rc (x_e rsegs cx))); su_in].
        - apply REGK4; [cbn [In]; tauto |
            apply (Hall (LReg 26, e_F (x_e rsegs cx) + HQU_RES)); su_in].
        - apply CELLR4; [lia | apply (Hall (LCell XR 0x18, e_F (x_e rsegs cx))); su_in].
        - apply CELLR4; [lia | apply (Hall (LCell XR 0x48, e_F (x_e rsegs cx))); su_in].
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_XO; lia). exact K138.
        - apply CELLR4; [lia |
            apply (Hall (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps)); su_in].
        - apply CELLR4; [lia | apply (Hall (LCell XR 0x148, e_pp (x_e rsegs cx))); su_in].
        - apply CELLR4; [lia |
            apply (Hall (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3)); su_in].
        - apply CELLR4; [lia | apply (Hall (LCell XR 0x158, e_pod (x_e rsegs cx))); su_in].
        - apply Forall_nil. }
      split; [exact Hcorr|].
      rewrite Hexp. cbn [ans_rc ans_cells ans_keys ans_rf fst snd length].
      split; [reflexivity | apply HXAT4; reflexivity].
    * (* 0 < n_ent: the pair loop's head, at index 0 *)
      apply (HPAIR (su_fx3 fx2) ly1 S1 W1 regs3 mem3 md3 [] 0 Headamp.REFUSE_NONE).
      split; [exact BASE3|].
      split.
      { unfold hsu_at_cx, hsu_at, hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_loopr, hqu_L_t56.
        rewrite <- !app_assoc. cbn [app].
        repeat apply Forall_cons; cbv beta; cbn [fst snd].
        - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 8, e_S (x_e rsegs cx))); su_in].
        - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 9, e_R (x_e rsegs cx))); su_in].
        - apply REGK; [cbn [In]; tauto |
            apply (Hall (LReg 19, shadow_addr (e_F (x_e rsegs cx)))); su_in].
        - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 27, SHADOW_OFF)); su_in].
        - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 20, e_cap (x_e rsegs cx))); su_in].
        - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 22, e_out (x_e rsegs cx))); su_in].
        - apply REGK; [cbn [In]; tauto | apply (Hall (LReg 25, e_rc (x_e rsegs cx))); su_in].
        - apply REGK; [cbn [In]; tauto |
            apply (Hall (LReg 26, e_F (x_e rsegs cx) + HQU_RES)); su_in].
        - apply CELLR; [lia | apply (Hall (LCell XR 0x18, e_F (x_e rsegs cx))); su_in].
        - apply CELLR; [lia | apply (Hall (LCell XR 0x48, e_F (x_e rsegs cx))); su_in].
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold Layout.OFF_N_ENT; lia).
          exact K98.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_MHALF_HI; lia). exact KA0.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_HALF_HI; lia). exact KA8.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_C2HI; lia). exact KB0.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_C2LO; lia). exact KB8.
        - unfold hd_at. cbn [hd_xv]. exact KC0.
        - unfold hd_at. cbn [hd_xv].
          rewrite Z.mod_small by (unfold HQU_XO, HQU_X_CELL0; lia). exact KC8.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_RC_BIG; lia). exact KD0.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_MUL104; lia). exact K118.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold Layout.OFF_N_ENT; lia).
          exact K120.
        - unfold hd_at. cbn [hd_xv]. unfold hqu_not.
          replace (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)
            with (e_pp (x_e rsegs cx) + 0x401c) by (unfold Layout.OFF_ENT; lia).
          exact K128.
        - unfold hd_at. cbn [hd_xv].
          rewrite Z.mod_small by (unfold shadow_addr, SHADOW_OFF, Layout.OFF_N_ENT; lia).
          exact K130.
        - unfold hd_at. cbn [hd_xv]. rewrite Z.mod_small by (unfold HQU_XO; lia). exact K138.
        - apply CELLR; [lia |
            apply (Hall (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps)); su_in].
        - apply CELLR; [lia | apply (Hall (LCell XR 0x148, e_pp (x_e rsegs cx))); su_in].
        - apply CELLR; [lia |
            apply (Hall (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3)); su_in].
        - apply CELLR; [lia | apply (Hall (LCell XR 0x158, e_pod (x_e rsegs cx))); su_in].
        - unfold hd_at. unfold Layout.OFF_ENT. exact G5.
        - unfold hd_at. replace (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4)
            with (e_pp (x_e rsegs cx) + 0x4018) by (unfold Layout.OFF_ENT; lia). exact G6.
        - unfold hd_at. unfold hqu_not, Layout.OFF_ENT, w64 in G7 |- *.
          rewrite HPgSteps.Z_to_bv_mod64 in G7. exact G7.
        - unfold hd_at. replace (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)
            with (e_pp (x_e rsegs cx) + 0x401c) by (unfold Layout.OFF_ENT; lia). exact G28.
        - unfold hd_at. replace (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)
            with (e_pp (x_e rsegs cx) + 0x401c) by (unfold Layout.OFF_ENT; lia). exact G29.
        - unfold hd_at. unfold Layout.OFF_PARAMS_STRUCT. exact G30.
        - unfold hd_at. unfold Layout.OFF_PARAMS_STRUCT. exact G31.
        - unfold hd_at. cbn [Z.of_nat]. exact G12.
        - unfold hd_at. exact G21.
        - apply Forall_nil. }
      split; [exact (proj1 HFS)|].
      split; [exact (proj1 (proj2 HFS))|].
      split; [exact (proj2 (proj2 HFS))|].
      split; [exact Hlive|].
      split; [unfold hqu_nent in *; lia|].
      split; [cbn [length]; lia|].
      split; [apply HXAT; reflexivity | exact Hfold].
Qed.
End asm.

Print Assumptions hqu_M3a_setup.
