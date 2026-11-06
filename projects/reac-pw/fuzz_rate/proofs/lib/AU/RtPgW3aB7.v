(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 344 of its 383 lines of code are new or changed and 430 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW3b.v at 4d659c905bca (its shape-7 part:
   w3b_b7_core, w3b_img_b7, w3b_b7_img and rs_piece_W3b_b7), for the same unit's image B: image B's pcs and code; the
   values the header reads come from real-frame cells (pp at R+0x168, &pp->len at R+0x158, the shadow address of
   &pp->len at R+0x170, ~pp at R+0x108) and pp is the register a6; the two UBSan tests of pod_put32 (pod.h:179) and
   the shape-7 flag store R+0x110 are new; the statement is lib/AU/RtPgSegB.v's rsb_piece_W3b_b7_stmt. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the shape-7 header piece of
   the build (M01) of LLVMFuzzerTestOneInput 0x8076c, B7 0x80c80 -> PH 0x80ea0. Proves no function (kind: segment
   lemma).

   THE CODE (pod.h:389-391, shape = 7: pod_put32(pp, POD_STRUCT = 14))
     0x80c80  a3 = -0x4001; R+0x110 := 1 (the shape-7 flag)
     0x80c90  bltu a2,a3 -> PH        a2 = len - 0x3ffd with len = 4: the capacity test, decided on literals, falls
                                      through
     0x80c94  a2 = 16385; 0x80c9c bltu a0,a2 (a0 = len = 4)      the UBSan bound of the put, decided on literals
     0x80ca4  ld a2,0x108(s1) (= ~pp); 0x80ca8 bgeu a2,a0        the UBSan pointer test, decided by ~pp's range
     0x80cb0  a0 = pp + 4 (pp from R+0x168); the two store checks of pp + 4 and pp + 7; four stores 14, 0, 0, 0
     0x80cf8  ld a0,0x170(s1) / lbu a0,0(a0): the check of pp->len through its shadow address
     0x80d08  len := len + 4 = 8 through &pp->len in R+0x158; 0x80d18 j PH
   Every other arm of the five tests is the `unimp` at 0x83098 or the report call of an instrumented check; each is
   decided here, so no arm of this piece is run.

   HOW. The piece rebuilds a symbolic state at B7 from the cut (the registers as their own atoms, a0 = 4 and
   a2 = 4 - 0x3ffd as literals; the real-frame cells as regions whose chunks are pp's atom x16, its expressions and
   the extra atom 32 for ~pp, whose closed range [2^63, 2^64 - 1] decides the pointer test) and runs the kit's token
   engine (lib/Reusable/YCbn.v through YCbq.aj_run_to_tok) with one shadow entry, pp's 19744 bytes on x16; the shadow
   base is s4 = x20, whose atom has the exact range [SHADOW_OFF, SHADOW_OFF]. The engine reads every shadow byte of
   the header as the literal 0, so no check leaves an obligation and no slow block is run. The stores into pp are
   allowed by the journal through RtPgBase.rt_fresh_awr (pp is not live at the harness entry: RtPgCSpec.rt_seg_pre's
   pp conjunct); the store into R+0x110 by the journal's stack window. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
From OSSVerify.reac_pw.fuzz_rate.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* image B's loaded segments *)
Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ===================================== the engine's context ===================================== *)
Definition W3S_B7 : Z := 0x80c80.
Definition W3S_PH : Z := 0x80ea0.
(* the 137 instruction words 0x80c80 .. 0x80e9c *)
Definition w3s_tbl : ctable := build_table rsegs W3S_B7 137 TEmpty.
Lemma w3s_tbl_ok : table_ok rsegs w3s_tbl.
Proof. apply build_table_ok0. unfold W3S_B7. lia. Qed.
(* the shadow base is x20 (s4) *)
Definition w3s_Bx : sv := SOff 20 0.
Definition w3s_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* pp on x16 (a6), its 19744 bytes *)
Definition w3s_SH : list shent := [mkSHE 16 0 19744].
Definition W3S_PPHI : Z := 0x7fffff800000 - 19744.
Definition W3S_RLO : Z := 0x7fff7f800000.
(* the shadow address of &pp->len, as the build put it in R+0x170 (0x80ba0 .. 0x80ba8) *)
Definition w3s_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 16 16384) (SLit 3)) (SOff 20 0).
Definition W3S_A2 : Z := 0xffffffffffffc007.    (* 4 - 0x3ffd mod 2^64 *)
Definition W3S_NLO : Z := 0x8000000000000000.   (* 2^63: the least ~pp *)
Definition W3S_NHI : Z := 0xffffffffffffffff.
Definition w3s_atoms : list (nat * afact) :=
[(16%nat, mkAF 4096 W3S_PPHI 0); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (9%nat, mkAF W3S_RLO (2 ^ 47) 0);
 (32%nat, mkAF W3S_NLO W3S_NHI 0)].
(* a0 = len = 4 and a2 = len - 0x3ffd are literals; every other register is its own atom *)
Definition w3s_regs : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit 4)) (Z_to_bv 5 12) (SLit W3S_A2).
(* the real-frame cells: ~pp (read), the shape-7 flag (written), &pp->len, pp and the shadow address of &pp->len *)
Definition w3s_rN : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [YP09.mkChunk 0x108 (CVal 8 (SOff 32 0))].
Definition w3s_rF : YP09.region := YP09.mkRegion (Some 9%nat) 0x110 0x118 0x110 0x118 [].
Definition w3s_rP : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x158 0x178 0 0
[YP09.mkChunk 0x158 (CVal 8 (SOff 16 16384)); YP09.mkChunk 0x168 (CVal 8 (SOff 16 0));
 YP09.mkChunk 0x170 (CVal 8 w3s_shx)].
(* pp's header word (written only) and &pp->len with len = 4 *)
Definition w3s_rH : YP09.region := YP09.mkRegion (Some 16%nat) 4 8 4 8 [].
Definition w3s_rL : YP09.region :=
YP09.mkRegion (Some 16%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SLit 4))].
Definition w3s_ss : sstate :=
mkSS W3S_B7 w3s_regs [w3s_rN; w3s_rF; w3s_rP; w3s_rH; w3s_rL] None (mkFacts w3s_atoms [] []).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* a register the final symbolic state still holds as its own atom keeps its value *)
Lemma w3s_reg_kept : forall E ss ms regs0 extra (H : word -> bool) (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H r HS HA Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr. rewrite HA by lia. apply ew_Ereg_reg.
Qed.

(* one byte a run stored, as the walk reads it back: a CVal 1 chunk of a final region at base + off *)
Lemma w3s_chunk1 : forall E (H : word -> bool) ms base off e (b : byte),
YP09.chunk_ok rsegs E (ms_mem (restrict H ms)) base (YP09.mkChunk off (CVal 1 e)) ->
byte_of_word (sv_denot E e) 0 = b -> forall a, a = base + off -> aview rsegs H (ms_mem ms) a = Some (bv_unsigned b).
Proof.
intros E H ms base off e b C Hb a ->. destruct (C 0 ltac:(cbn; lia)) as (b' & H1 & H2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in H1, H2. injection H1 as <-. rewrite Z.add_0_r in H2.
unfold aview. change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)). rewrite H2, Hb. reflexivity.
Qed.

(* the registers the piece leaves alone: all but a0, a2, a3, a4 *)
Definition W3S_KEPT : list Z :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

Ltac w3s_kept_regs HS HAE E ms regs extra W :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [W3S_KEPT] in Hr;
repeat (destruct Hr as [<-|Hr];
  [eapply (w3s_reg_kept E _ ms regs extra (w_H W)); [exact HS | exact HAE | vm_compute; reflexivity] |]);
destruct Hr.

(* the chunk of R+0x170 is the shadow address of &pp->len *)
Lemma w3s_shx_val : forall E pp, ew E 16 = Z_to_bv 64 pp -> ew E 20 = Z_to_bv 64 SHADOW_OFF ->
4096 <= pp -> pp + 19744 <= 0x7fffff800000 ->
sv_denot E w3s_shx = Z_to_bv 64 (shadow_addr (pp + 0x4000) mod 2 ^ 64).
Proof.
intros E pp E16 E20 Hp0 Hp1.
unfold w3s_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E 16 pp 16384 E16) by lia.
rewrite (U_atom E 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold shadow_addr, zcanon, M64.
assert (Hd : 0 <= (pp + 16384) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (Z.mod_small ((pp + 16384) / 8)) by lia.
rewrite (Z.mod_small ((pp + 16384) / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
rewrite (Z.mod_small (SHADOW_OFF + (pp + 16384) / 8)) by (unfold SHADOW_OFF; lia).
f_equal. lia.
Qed.

(* ===================================== B7 -> PH: the shape-7 header =====================================
   Entry facts: s1 = R, a0 = len = 4, a2 = len - 0x3ffd, a6 = pp, s4 = SHADOW_OFF; the cells R+0x108 (~pp), R+0x158
   (&pp->len), R+0x168 (pp), R+0x170 (the shadow address of &pp->len); len = 4 in pp. At 0x80ea0: a0, a2, a3, a4
   changed, the four header bytes at pp + 4, len = 8, R+0x110 = 1, every other byte as before. *)
Lemma w3s_b7_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k
(regs : bvmap 5 word) (R pp : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (pp, PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
sp0 - STK <= R -> R + 0x220 <= sp0 -> W3S_RLO <= R ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 4 ->
getr regs (Z_to_bv 5 12) = w64 (4 - 0x3ffd) -> getr regs (Z_to_bv 5 16) = w64 pp ->
getr regs (Z_to_bv 5 20) = w64 SHADOW_OFF ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (Z.lnot pp mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 ((pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 (pp mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 4 ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
 same_io mdc md2 ->
 (forall r, In r W3S_KEPT -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 4 <= a < pp + 8) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  ~ (R + 0x110 <= a < R + 0x118) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 rtmb_bytes rsegs (w_H W) mem2 (pp + 4) (hdr_bytes 7) ->
 rtmb_bytes rsegs (w_H W) mem2 (pp + 0x4000) (le64 8) ->
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x110) 8 1 ->
 SRr rsegs W (cfg_at rsegs W3S_PH regs2 mem2 md2) Q) ->
SRr rsegs W (cfg_at rsegs W3S_B7 regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp Q HJ Hin Hout HR0 HR1 HRlo
  R9 R10 R12 R16 R20 V108 V158 V168 V170 Vlen KONT.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RtPgStepsB.rtsb_wx as Hwx. pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hin) as (_ & Hpp0 & Hppc & Happ & Hppr & _).
rewrite Erq in Hppc, Happ, Hppr.
unfold W3S_RLO in HRlo.
assert (Hl : Z.lnot pp = (2 ^ 64 - 1 - pp) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
assert (Hnpp : Z.lnot pp mod 2 ^ 64 = 2 ^ 64 - 1 - pp)
  by (rewrite Hl, Z_mod_plus_full; apply Z.mod_small; lia).
set (npp := Z.lnot pp mod 2 ^ 64) in *.
remember (Ereg regs [Z_to_bv 64 npp]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 npp]) n) by (intros; subst E; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 npp) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = R)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U16 : bv_unsigned (ew E 16) = pp)
  by (rewrite (EE 16%nat (Z_to_bv 5 16) eq_refl), R16; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = npp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E16 : ew E 16 = Z_to_bv 64 pp) by (rewrite <- U16; symmetry; apply Z_to_bv_bv_unsigned).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite <- U20; symmetry; apply Z_to_bv_bv_unsigned).
(* the symbolic state at B7 *)
assert (HS : st_ok rsegs E w3s_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 W3S_B7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3s_ss. apply (entry_st_ok_full rsegs).
  - unfold w3s_regs.
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite R10. reflexivity.
    + rewrite R12. unfold w64. cbn [sv_denot]. apply Z_to_bv64_eq_mod. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. repeat apply Forall_cons; try apply Forall_nil.
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ R 0x108 8 (SOff 32 0) npp); [| cbn; lia | cbn; lia | exact V108].
      cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + apply (rtmb_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hstkp; lia |].
      apply Forall_nil.
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 16 16384) ((pp + 0x4000) mod 2 ^ 64));
          [| pose proof (Z.mod_pos_bound (pp + 0x4000) (2 ^ 64) ltac:(lia)); cbn; lia | cbn; lia | exact V158].
        apply bv_eq. rewrite denot_SOff, E16. rewrite unsigned_lit_small by lia.
        rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
      * apply (chunk_ok_val rsegs E _ R 0x168 8 (SOff 16 0) (pp mod 2 ^ 64));
          [| pose proof (Z.mod_pos_bound pp (2 ^ 64) ltac:(lia)); cbn; lia | cbn; lia | exact V168].
        apply bv_eq. rewrite denot_SOff, E16. rewrite unsigned_lit_small by lia.
        rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
      * apply (chunk_ok_val rsegs E _ R 0x170 8 w3s_shx (shadow_addr (pp + 0x4000) mod 2 ^ 64));
          [| pose proof (Z.mod_pos_bound (shadow_addr (pp + 0x4000)) (2 ^ 64) ltac:(lia)); cbn; lia
           | cbn; lia | exact V170].
        apply w3s_shx_val; [exact E16 | exact E20 | lia | unfold in_app, kLowShadowBeg, kHighMemBeg in Happ; lia].
    + unfold region_ok, w3s_rH. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U16. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (Hppr (pp + o) ltac:(lia))).
    + unfold region_ok, w3s_rL. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U16. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply (proj1 (Hppr (pp + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SLit 4) 4);
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia | exact Vlen].
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val w3s_rN w3s_rF w3s_rP w3s_rH w3s_rL]. rewrite U9, U16.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. repeat split; lia.
  - rewrite <- HE. split; [|split; exact I].
    cbn [f_atoms w3s_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U16, U20, U9, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold W3S_PPHI, W3S_RLO, W3S_NLO, W3S_NHI, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs w3s_Bx w3s_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, w3s_SH. repeat apply Forall_cons; try apply Forall_nil.
  unfold shent_ok, app_apart, w3s_Bx. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E 16 pp E16) by lia.
  split.
  + change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
    apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE);
      [exact HAR | exact Hin | lia | rewrite Erq; lia].
  + intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
clear HE.
unfold cfg_at. change (w64 W3S_B7) with (Z_to_bv 64 W3S_B7).
aj_run_to_tok w3s_tbl_ok HS HJ SHOK w3s_Bspan W3S_PH.
{ (* the run writes the shape-7 flag in the real frame, pp's header word and pp->len *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 16%nat pp); [reflexivity | exact U16 | |];
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_wlo YP09.r_whi] in Ha; replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia] | ]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
    [reflexivity | refine (eq_trans U9 _); lia | cbn; lia | cbn; lia |] ]. }
(* ---- the state at 0x80ea0 ---- *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem] in HOK.
pose proof (Forall_inv (Forall_inv_tail HOK)) as (_ & _ & _ & Cf).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HOK)))) as (_ & _ & _ & Ch).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HOK)))))
  as (_ & _ & _ & Cl).
cbn [YP09.r_base YP09.r_chunks base_val] in Cf, Ch, Cl. rewrite U9 in Cf. rewrite U16 in Ch, Cl. clear HOK.
repeat rewrite Forall_cons_iff in Cf. repeat rewrite Forall_cons_iff in Ch.
repeat rewrite Forall_cons_iff in Cl.
destruct Cf as (Cflag & _).
destruct Cl as (Clen & _).
destruct Ch as (C7 & C6 & C5 & C4 & _).
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply (KONT (ms_regs ms) (ms_mem ms)).
- exact HJ.
- apply RtPgStepsB.same_io_wvb.
- w3s_kept_regs HS HAE E ms regs [Z_to_bv 64 npp] W.
- intros a Ha Ha1 Ha2 Ha3. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hr & Hb).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U16 in Hb; lia | ]).
  destruct Hr.
- (* the four header bytes, one CVal 1 chunk each *)
  apply (proj2 (rtmb_bytes_aview rsegs (w_H W) (ms_mem ms) (pp + 4) (hdr_bytes 7))). intros i Hi. cbn in Hi.
  do 4 (destruct i as [|i];
    [ match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 _)) |- _ =>
        eapply (w3s_chunk1 E (w_H W) ms pp o _ _ C);
        [ | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia];
        cbn [sv_denot]; vm_compute; reflexivity end | ]); lia.
- (* len = 8 *)
  apply rtmb_bytes_of_val.
  exact (val_of_chunk_ok rsegs E _ pp 0x4000 8 (SLit 8) 8 Clen eq_refl
    ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)).
- (* the shape-7 flag *)
  exact (val_of_chunk_ok rsegs E _ R 0x110 8 (SLit 1) 1 Cflag eq_refl
    ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)).
Qed.

(* ===================================== the block's bytes at PH =====================================
   pc_image of the empty record of shape 7: B7's image (the top size word only) with the Struct word at 4 and
   len = 8 at 0x4000. *)
Lemma w3s_img_b7 :
pc_image (PbCut 7 [] None) =
overwrite (rtmb_slice rsb_img_hdr 0 16384) 4 (hdr_bytes 7) ++ le64 8 ++ rtmb_slice rsb_img_hdr 16392 3352.
Proof. vm_compute. reflexivity. Qed.
Lemma w3s_b7_img : forall H mem H' mem' pp,
rtmb_bytes rsegs H mem pp rsb_img_hdr ->
rtmb_bytes rsegs H' mem' (pp + 4) (hdr_bytes 7) ->
rtmb_bytes rsegs H' mem' (pp + 16384) (le64 8) ->
(forall y, pp <= y < pp + 19744 -> ~ (pp + 4 <= y < pp + 8) -> ~ (pp + 16384 <= y < pp + 16392) ->
 aview rsegs H' mem' y = aview rsegs H mem y) ->
rtmb_bytes rsegs H' mem' pp (pc_image (PbCut 7 [] None)).
Proof.
intros H mem H' mem' pp B0 Bh Bl K.
rewrite w3s_img_b7.
assert (L0 : length rsb_img_hdr = 19744%nat) by (vm_compute; reflexivity).
assert (L1 : length (rtmb_slice rsb_img_hdr 0 16384) = 16384%nat) by (vm_compute; reflexivity).
assert (L2 : length (rtmb_slice rsb_img_hdr 16392 3352) = 3352%nat) by (vm_compute; reflexivity).
assert (Lh : length (hdr_bytes 7) = 4%nat) by reflexivity.
assert (Lo : length (overwrite (rtmb_slice rsb_img_hdr 0 16384) 4 (hdr_bytes 7)) = 16384%nat)
  by (rewrite length_overwrite; [exact L1 | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity]).
apply rtmb_bytes_app. split.
- pose proof (rtmb_bytes_slice rsegs H mem pp rsb_img_hdr 0 16384 B0
    ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bb.
  change (Z.of_nat 0) with 0 in Bb. rewrite Z.add_0_r in Bb.
  apply (rtmb_bytes_patch rsegs H mem H' mem' pp _ 4 _ Bb);
    [exact Bh | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity |].
  rewrite Lh, L1. intros y Hy Hn. change (Z.of_nat 16384) with 16384 in Hy.
  change (Z.of_nat 4) with 4 in Hn. change (Z.of_nat (4 + 4)) with 8 in Hn. apply K; lia.
- rewrite Lo. change (Z.of_nat 16384) with 16384. apply rtmb_bytes_app. split; [exact Bl|].
  change (length (le64 8)) with 8%nat. change (Z.of_nat 8) with 8.
  pose proof (rtmb_bytes_slice rsegs H mem pp rsb_img_hdr 16392 3352 B0
    ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bt.
  change (Z.of_nat 16392) with 16392 in Bt. replace (pp + 16384 + 8) with (pp + 16392) by lia.
  apply (rtmb_bytes_kept rsegs H mem H' mem' _ _ Bt). rewrite L2. change (Z.of_nat 3352) with 3352.
  intros y Hy. apply K; lia.
Qed.

(* ===================================== the piece statement =====================================  *)
Section e.
Variable MT : ameter_ops.

Ltac w3s_in_kept := unfold W3S_KEPT; cbn [In]; lia.

(* B7 -> PH *)
Theorem rt_B_piece_W3b_b7 : rsb_piece_W3b_b7_stmt rsegs B MT.
Proof.
intros cx POST rest HST HPH ly2 S2 W2 regs2 mem2 md2 r np HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct HST as (HPRE & _ & _ & _ & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & Hppc & _ & _ & _ & _ & _ & _ & _
  & Hfresh & _ & _).
cbn [hi_rsz hi_cid rate_himg_B] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
(* the bounds of R, pp and F *)
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 4) with 1024 in HFc.
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
assert (Hin2 : In (q_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppc]).
(* the facts of B7's location list *)
unfold rsb_at_cx, rsb_at, rsb_L_hdr, rsb_Hch, rsb_cur2 in HAT. cbn [app] in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A10 & A12 & A16 & A17 & A22 & A8 & A9 & A19 & A20 & C158 & A24 & A25 & C168 & C50 & C118 & C170 &
  C120 & A11 & C108 & C48 & C30 & C38 & C40 & A26 & C148 & A18 & A29 & _).
pose proof A9 as Q9. pose proof A10 as Q10. pose proof A12 as Q12. pose proof A16 as Q16. pose proof A20 as Q20.
pose proof C108 as D108. pose proof C158 as D158. pose proof C168 as D168. pose proof C170 as D170.
cbn [fst snd rt_at rt_xv] in Q9, Q10, Q12, Q16, Q20, D108, D158, D168, D170.
pose proof (rtmb_pp_len rsegs (le32 0) false false false [] false ltac:(unfold POD_BUF_MAX; rewrite length_le32; lia)
  ltac:(cbn; lia) ltac:(constructor) (w_H W2) mem2 (q_pp (x_e cx)) HPP) as Vlen.
unfold OFF_LEN in Vlen. rewrite length_le32 in Vlen. cbn [Z.of_nat Pos.of_succ_nat] in Vlen.
assert (HR0 : x_sp0 cx - x_STK cx <= q_R (x_e cx)) by lia.
assert (HR1 : q_R (x_e cx) + 0x220 <= x_sp0 cx) by lia.
assert (HRlo : W3S_RLO <= q_R (x_e cx)) by (unfold W3S_RLO; lia).
eapply (w3s_b7_core _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 _ regs2 (q_R (x_e cx)) (q_pp (x_e cx)) POST
  HJ Hin2 Hfresh HR0 HR1 HRlo Q9 Q10 Q12 Q16 Q20 D108 D158 D168 D170 Vlen).
intros regs3 mem3 md3 HJ3 Hio3 HK3 HM3 Bh Bl V110.
apply (HPH ly2 S2 W2 regs3 mem3 md3 r 7 np).
unfold rsb_cut_PH. split; [|split; [|split; [|split]]].
- (* the journal and the kept bytes *)
  unfold rsb_core, rsb_mid. split; [exact HJ3|].
  split; [intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]]; apply HK3; w3s_in_kept|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
  split; [exact Hmo|].
  intros a Ha HnS HnE. rewrite <- (Hkeep a Ha HnS HnE).
  apply HM3; [exact Ha | | |]; intros X; apply HnE.
  + right. unfold PP_SIZE. lia.
  + right. unfold PP_SIZE. lia.
  + left. unfold rt_inw. cbn [hi_w1 rate_himg_B].
    apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- (* PH's location list: B7's without a0 and a2, each kept, plus the shape-7 flag *)
  unfold rsb_at_cx, rsb_at, rsb_L_PH, rsb_Hch, rsb_cur2. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  first
  [ cbn [rt_at rt_xv]; change (Z.b2z (7 =? 7) mod 2 ^ 64) with 1; exact V110
  | eapply (rtmb_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3); [eassumption|];
    cbn [rtmb_keeps rt_xv]; first [apply HK3; w3s_in_kept | intros i Hi; apply HM3; lia] ].
- (* the frame's shadow: no byte of it is written *)
  apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 _ rsb_P0 HFSH).
  intros i Hi. change (Z.of_nat (length rsb_P0)) with 88 in Hi.
  assert (Hd : 0 <= q_F (x_e cx) / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
  apply HM3; unfold shadow_addr, SHADOW_OFF; lia.
- (* the block holds the empty record of shape 7 *)
  apply (w3s_b7_img (w_H W2) mem2 (w_H W2) mem3 _ HPP Bh Bl).
  intros y Hy Hn1 Hn2. apply HM3; lia.
- split; [exact HIN|]. split; [exact HSUF|]. split; [exact Esh|]. split; [exact Enp | exact Er].
Qed.
End e.
End d.
End b.

Print Assumptions rt_B_piece_W3b_b7.
