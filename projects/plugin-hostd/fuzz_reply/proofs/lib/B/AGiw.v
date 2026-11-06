(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGiw.v (commit 30a1993588f, c5 + memnorm; file sha256 0b5b8464b6a9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 3 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/AGiw.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (3 numerals; per-numeral report). *)
(* The seed of the g-path MISS arm of the frame-generic Allocate walk: the walk's environment E0 satisfies
   AGi4.MS_1 at Allocate's entry, where the registers [regsU] are REGS_G over the virtual regs0 (as AGj0.SEED_ok) and
   the memory is read through the miss view [mview] (no allocator model).  Ported from the released YFiw (SEEDM_ok
   over the model ARm) with the caller's frame made abstract: AGj0's header, AGiz's region script for the regions
   MS_1 shares with SSG, the zero class count instead of the cache cells. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFhy YFhm AGhy AGhz AGis AGif0reply AGiz AGj0 AGi4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].

(* PENDING (G-MISS interface proposal, gmiss-iface-proposal.v.txt (sha256 e7caabcf2f8a; internal record)): the miss view.  It moves to AGif0n.v
   (owner TkIface) with the field if_mview; this local copy is deleted then.  The cells the miss seed MS_1 reads
   (AGi4.MREG0): hview's layout / image / tsd / constant cells / instance fields / unwinding byte, and the class
   count = 0 (no cached chunk, no shadow, no junk: those regions of MREG0 are bare). *)
Record mview (B : asyms) (W : world tfibsegs) (ly : alayout) (inst : Z) (mem : word -> option byte) (cl : Z) : Prop := {
  mv_ly : layout_ok ly;
  mv_img : img_cover ly;
  mv_tsd : ly_tsd ly = TFIB_TSD;
  mv_const : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly);
  mv_inst : val_mem tfibsegs (mrestrict (w_H W) mem) (inst + 0x20) 8 (ly_space ly) /\
            val_mem tfibsegs (mrestrict (w_H W) mem) (inst + 0xe20) 8 0x10000000000 /\
            val_mem tfibsegs (mrestrict (w_H W) mem) (inst + 0xe28) 8 0x108000010;
  mv_cnt0 : val_mem tfibsegs (mrestrict (w_H W) mem) (AGis.Pv ly cl) 4 0;
  mv_unw : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0
}.

Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AGis.RZ kz).
Local Abbreviation R8v := (@AGis.R8v n).
Local Abbreviation N8D := (@AGis.N8D n).
Local Abbreviation Pv := (@AGis.Pv ly cl).
Local Abbreviation PVv := (@AGis.PVv ly cl cnt).
Local Abbreviation Kv := (@AGis.Kv ly cl v).
Local Abbreviation SHBv := (@AGis.SHBv).
Local Abbreviation SKv := (@AGis.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGis.SSLOTv ly cl).
Local Abbreviation PBv := (@AGis.PBv ly n cl v kz).
Local Abbreviation Uv := (@AGis.Uv ly cl v kz).
Local Abbreviation SUv := (@AGis.SUv ly cl v kz).
Local Abbreviation FILv := (@AGis.FILv n).
Local Abbreviation NDv := (@AGis.NDv n kz).
Local Abbreviation E0 := (@AGis.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaT := (@AGis.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaC := (@AGis.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSB := (@AGis.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaTOP := (@AGis.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation Er := (@AGis.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E2 := (@AGis.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E10 := (@AGis.E10 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E11 := (@AGis.E11 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaP := (@AGis.EaP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaK := (@AGis.EaK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSK := (@AGis.EaSK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSSLOT := (@AGis.EaSSLOT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPB := (@AGis.EaPB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPV := (@AGis.EaPV ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaKL := (@AGis.EaKL ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaRZ := (@AGis.EaRZ ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaU := (@AGis.EaU ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSU := (@AGis.EaSU ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaFIL := (@AGis.EaFIL ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaND := (@AGis.EaND ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hcf1 : getr regs0 15 = w64 1.
Variable DPOST : Z -> (word -> option byte) -> Prop.
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Variables (B : asyms) (inst : Z).
Hypothesis TS : TfibSyms B.
Hypothesis HMV : mview B W ly inst mem0 cl.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis HIO : inst_ok inst.
Let m0 := mrestrict (w_H W) mem0.
Hypothesis PSO : val_mem tfibsegs m0 SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs m0 (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Variable regsU : bvmap 5 word.
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.
Hypothesis HU10 : getr regsU 10%bv = getr regs0 11%bv.
Hypothesis HU11 : getr regsU 11%bv = getr regs0 10%bv.
Hypothesis HU12 : getr regsU 12%bv = w64 8.
Hypothesis HU14 : getr regsU 14%bv = w64 1.
Local Abbreviation tr_length := (@AGis.tr_length tr Htrlen).
Local Abbreviation Kv_range := (@AGis.Kv_range ly regs0 mem0 n tr cl v kz Hcl Hv Hv2 Htrlen DPOST).
Local Abbreviation high_facts := (@AGis.high_facts _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation off_T := (@AGis.off_T _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation off_C := (@AGis.off_C _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation off_NB := (@AGis.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AGis.off_SB _ ly LY IMG).
Local Abbreviation RZ_facts := (@AGis.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@AGis.RZ_num n kz Hkz Nrange).
Local Abbreviation derived_ranges := (@AGis.derived_ranges _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation NDv_facts := (@AGis.NDv_facts ly regs0 mem0 n tr v kz Htrlen DPOST Hkz Nrange).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].

(* The miss view's constant cells (AGiz.vw_cell_lit / vw_cell_sym over [mview]). *)
Lemma mv_cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
val_mem tfibsegs m0 a w x.
Proof.
intros a w x E. apply (cell_holds_val_mem B ly (w_H W) mem0 (ANum a) w (ANum x)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly)) (mv_const _ _ _ _ _ _ HMV)).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma mv_cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros e w e' E. apply (cell_holds_val_mem B ly (w_H W) mem0 e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly)) (mv_const _ _ _ _ _ _ HMV)).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma chunk_lit : forall a (nn : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal nn (SLit x))).
Proof. intros a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | rewrite Z.add_0_l; exact H]. Qed.
Lemma chunk_lit_at : forall base a (nn : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SLit x))).
Proof. intros base a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | exact H]. Qed.
Lemma chunk_atom : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SOff k d))).
Proof.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| exact Hx | exact Hnn | exact H].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply mv_cell_lit; vm_compute; reflexivity | cbn; zlia | cbn; zlia] |]); apply Forall_nil.
Local Ltac bare_region := reg_intro; rewrite ?EaT, ?EaP, ?EaPV, ?EaK, ?EaU, ?EaSK, ?EaSSLOT; unfold w64; rewrite ?unsigned_lit_small by zlia;
split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia | apply Forall_nil].

(* The class-region geometry at v (no view: from AGis's ranges, as the released YFiw.FACTSM_ok). *)
Lemma Kv32M : Kv mod 32 = 0.
Proof.
pose proof (lo_space_al ly LY) as SAL. apply Z.mod_divide in SAL as [q Hq]; [|zlia]. apply Z.mod_divide in Hv2 as [w Hw]; [|zlia].
unfold AGis.Kv. rewrite Hq, Hw. apply Z.mod_divide; [zlia|]. exists (q * 2048 + cl * 2 ^ 27 + w). zlia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions of MS_1: AGhy's frame regions, then tl MREG0 (TAIL0G's first 37 regions, the unwinding region, the
   zero count region, the rest bare).                                                                               *)
Lemma REGM_ok : Forall (region_ok tfibsegs E0 m0) (R_soG :: R_scrG :: R_slotG :: tl MREG0).
Proof.
pose proof HMV as [HLY HIMG HTSD HCONST HINST HCNT0 HUNW].
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
destruct HIO as (IO1 & IO2 & IO3).
assert (EI : bv_unsigned (ew E0 11) = inst) by (rewrite E11, Hi11; unfold w64; apply unsigned_lit_small; zlia).
assert (ESO : bv_unsigned (ew E0 13) = SOv) by (rewrite (Er 13 13%bv eq_refl); reflexivity).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
rewrite MREG0_eq. unfold MTAIL0, RG0.
unfold R_soG, R_scrG, R_slotG, TAIL0G, iatom8, ilits8, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE, bare.
cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add firstn skipn nth tl app].
unfold aSB, aSHB, aC, aT, aTOP, aJ0, aJ1, aJ2, aJ3, aJ4, aCNT, aCSZ, aV, aJB, aSK, aP, aPV, aK, aU, aSSLOT, aINST, aSO, aBP, aLEN.
(* the stack object at aSO: the buffer pointer and the trace length *)
apply Forall_cons.
{   reg_intro. rewrite ESO. pose proof (u64_range (getr regs0 13)) as U13.
split; [unfold SOv; zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom SOv 0 8 12%nat 0 BPv);
[ rewrite Z.sub_0_r, (Er 12 12%bv eq_refl); unfold w64, BPv; symmetry; apply Z_to_bv_bv_unsigned
| pose proof (u64_range (getr regs0 12)); unfold BPv; zlia | rewrite Z.add_0_r; exact PSO
| unfold BPv; pose proof (u64_range (getr regs0 12)); change (8 * Z.of_N 8) with 64; zlia | cbn; zlia ].
- apply (chunk_atom SOv 8 8 36%nat 0 (Z.of_nat (length tr))); [rewrite Z.sub_0_r; reflexivity | zlia | exact PLEN | change (8 * Z.of_N 8) with 64; zlia | cbn; zlia]. }
(* the scratch window below the entry sp *)
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- AFSTACK)); [rewrite E2; reflexivity | unfold AFSTACK; zlia | zlia |].
intros a Ha. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, AFSTACK in *; zlia) | apply Hpres0; exact Ha]. }
(* the empty slot *)
apply Forall_cons.
{   reg_intro. rewrite E2. pose proof (u64_range (getr regs0 2)). split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia | apply Forall_nil]. }
do 8 (apply Forall_cons; [lit_region|]).
(* the instance's primary.space field *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom inst 32 8 34%nat 0 SB); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | exact (proj1 HINST) | unfold SB; cbn; zlia | cbn; zlia]. }
(* the instance's words at +0xe20 *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
destruct HINST as (_ & HI2 & HI3).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; (apply chunk_lit_at; [assumption | cbn; zlia | cbn; zlia]). }
do 13 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 47%nat 0 SHBv); [reflexivity | unfold AGis.SHBv; zlia | | unfold AGis.SHBv; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. apply mv_cell_lit. vm_compute. reflexivity. }
do 7 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| cbn; zlia | cbn; zlia]. pose proof (mv_cell_lit 0x5d9a00 8 0 ltac:(vm_compute; reflexivity)) as H8.
intros k Hk. unfold m0 in *. rewrite (H8 k ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
apply Forall_cons; [lit_region|].
apply Forall_cons. {   reg_intro. unfold TFIB_TP. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; zlia | cbn; zlia].
replace (6134256 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; zlia). apply mv_cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. unfold TFIB_TSD. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 6270360 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply mv_cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (mv_cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; unfold T; zlia).
apply mv_cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; zlia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply mv_cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; zlia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; zlia). apply mv_cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP; unfold w64; f_equal; zlia | unfold kStackSpan; zlia | | unfold kStackSpan; cbn; zlia | cbn; zlia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; zlia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; zlia).
apply mv_cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; zlia). apply (mv_cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
(* MTAIL0: the junk word region (bare), the unwinding byte, two bare junk regions, the zero count, the rest bare *)
apply Forall_cons; [bare_region|].
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia. unfold t_unwinding.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. replace (ly_T ly + o) with (ly_T ly + 3168) by zlia.
pose proof HUNW as U.
eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. unfold t_unwinding in U. rewrite <- (Z.add_0_r (ly_T ly + 3168)). exact (U 0%nat ltac:(zlia)). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. exact HUNW. }
apply Forall_cons; [bare_region|].
apply Forall_cons; [bare_region|].
apply Forall_cons. {   reg_intro. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. rewrite Z.add_0_r. exact HCNT0. }
repeat (apply Forall_cons; [bare_region|]). apply Forall_nil.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions of MS_1 are pairwise disjoint: the extents are those of REG0G (AGj0.PAIRS_ok).                        *)
Lemma MS_1_skel : map ext3 REG0G = map ext3 (R_soG :: R_scrG :: R_slotG :: tl MREG0).
Proof. vm_compute. reflexivity. Qed.
Lemma PAIRSM_ok : pairwise_disjoint E0 (R_soG :: R_scrG :: R_slotG :: tl MREG0).
Proof.
apply (pairwise_disjoint_ext3 E0 REG0G _ MS_1_skel).
eapply AGj0.PAIRS_ok; first [eassumption | exact HIO].
Unshelve. all: first [exact md0 | exact csz | exact j0 | exact jb | exact j1 | exact j2 | exact j3 | exact j4 | exact DPOST].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The facts of FGG (AGj0.FACTS_ok's script, the class-region facts at v from AGis's ranges).                       *)
Lemma FACTSM_ok : facts_ok E0 FGG.
Proof.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
destruct HIO as (IO1 & IO2 & IO3).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
pose proof tr_length as TL. pose proof (lo_space_al ly LY) as SAL. pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL.
unfold page_aligned in TAL.
assert (V1 : 17594333495296 <= Kv) by (clear - HKR hf3 hf4; zlia). assert (V2 : Kv + 2 ^ 16 <= 140737479966720) by (clear - HKR hf5 hf6; zlia).
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; zlia. }
unfold facts_ok, FGG, frame_facts. cbn [f_atoms f_conds f_alias FG tl app atoms_ok conds_ok alias_ok].
split; [|split; exact I].
unfold aSB, aSHB, aC, aT, aTOP, aSK, aP, aPV, aK, aSSLOT, aLEN, aJ0, aR8, aCL, aCNT, aV, aCSZ, aJB, aJ1, aJ2, aJ3, aJ4, aPB, aN8D, aCNT8, aKL, aRZ, aH, aU, aSU, aFIL, aND,
aINST, aSO, aBP.
pose proof RZ_num as (RZr & RZ8 & RZ88 & Nlo & NRZ). pose proof Kv32M as K32. pose proof NDv_facts as (ND1 & ND2 & ND3 & ND4 & ND5).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AFSTACK.
(* the frame atoms: the entry sp, the instance, the stack object, the buffer, can_fill *)
split. { apply (AF 2%nat sp0); [exact E2'| | | |].
all: pose proof (u64_range (getr regs0 2)) as U; clear - U S1 S2 S3 S4 T1 T4 T7; unfold sp0, AFSTACK in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact S4]. }
split. { apply (AF 11%nat inst); [rewrite E11; exact Hi11| | | |].
all: clear - IO1 IO2 IO3; first [zlia | replace (2 ^ 3) with 8 by reflexivity; exact IO3]. }
split. { apply (AF 13%nat SOv); [rewrite (Er 13 13%bv eq_refl); unfold SOv, w64; symmetry; apply Z_to_bv_bv_unsigned| | | |].
all: pose proof (u64_range (getr regs0 13)) as U; clear - U Hso S1 S2 S3 T1 T4 T7; unfold SOv, sp0, AFSTACK in *;
first [zlia | replace (2 ^ 3) with 8 by reflexivity; exact (proj2 (proj2 Hso))]. }
split. { apply (AF 12%nat BPv); [rewrite (Er 12 12%bv eq_refl); unfold BPv, w64; symmetry; apply Z_to_bv_bv_unsigned| | | |].
all: pose proof (u64_range (getr regs0 12)) as U; clear - U Hbp S1 S2 S3 T1 T4 T7; unfold BPv, sp0, AFSTACK in *;
first [zlia | replace (2 ^ 3) with 8 by reflexivity; exact (proj2 (proj2 Hbp))]. }
split. { apply (AF 15%nat 1); [rewrite (Er 15 15%bv eq_refl); exact Hcf1| | | |]. all: first [zlia | reflexivity]. }
(* the released facts *)
split. { apply (AF 10%nat n); [rewrite E10, Hn; reflexivity| | | |].
all: clear - Nlo; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 32%nat T); [exact EaT| | | |].
all: clear - hf1 hf2 TAL; first [zlia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |].
all: clear - hf7 hf8 CAL; first [zlia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |].
all: clear - hf3 hf4 hf5 hf6 SAL; first [zlia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |].
all: clear - T1 T2 T3 T4 T7; first [zlia | exact T3]. }
split. { apply (AF 36%nat (Z.of_nat (length tr))); [reflexivity| | | |].
all: clear - TL; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 37%nat (j0 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j0; first [zlia | pose proof (Z.mod_pos_bound j0 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 38%nat R8v); [reflexivity| | | |].
all: clear - DR Nlo; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
split. { apply (AF 39%nat cl); [reflexivity| | | |].
all: clear - Hcl; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 40%nat Pv); [exact EaP| | | |].
all: clear - DR hf1 hf2 TAL; unfold AGis.Pv, t_cache in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 256 + 13 + 5 * cl); zlia]. }
split. { apply (AF 41%nat cnt); [reflexivity| | | |].
all: clear - Hcnt; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 42%nat v); [reflexivity| | | |].
all: clear - Hv; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 43%nat (csz mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - csz; first [zlia | pose proof (Z.mod_pos_bound csz (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 44%nat PVv); [exact EaPV| | | |].
all: clear - DR hf1 hf2 TAL Hcnt; unfold AGis.PVv, AGis.Pv, t_cache in *; first [zlia | replace (2 ^ 2) with 4 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 1024 + 56 + 20 * cl + (cnt - 1)); zlia]. }
split. { apply (AF 45%nat Kv); [exact EaK| | | |].
all: clear - V1 V2 K32; first [zlia | replace (2 ^ 5) with 32 by reflexivity; exact K32]. }
split. { apply (AF 46%nat jb); [reflexivity| | | |].
all: clear - Hjb; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 47%nat SHBv); [reflexivity| | | |].
all: clear; unfold AGis.SHBv; first [zlia | reflexivity]. }
split. { apply (AF 48%nat SKv); [exact EaSK| | | |].
all: clear - DR K32; unfold AGis.SKv, AGis.SHBv in *; first [zlia | replace (2 ^ 2) with 4 by reflexivity; apply Z.mod_divide in K32 as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (536862720 + q); rewrite Hq; replace (q * 32) with (q * 4 * 8) by zlia; rewrite Z.div_mul by zlia; zlia]. }
split. { apply (AF 49%nat (j1 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j1; first [zlia | pose proof (Z.mod_pos_bound j1 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 50%nat (j2 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j2; first [zlia | pose proof (Z.mod_pos_bound j2 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 51%nat (j3 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j3; first [zlia | pose proof (Z.mod_pos_bound j3 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 52%nat SSLOTv); [exact EaSSLOT| | | |].
all: clear - DR hf1 hf2 TAL; unfold AGis.SSLOTv, t_stats in *; first [zlia | replace (2 ^ 3) with 8 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 512 + 364 + cl); zlia]. }
split. { apply (AF 53%nat (j4 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j4; first [zlia | pose proof (Z.mod_pos_bound j4 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 54%nat PBv); [exact EaPB| | | |].
all: clear - DR; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 55%nat N8D); [reflexivity| | | |].
all: clear - DR Nlo; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
split. { apply (AF 56%nat (N8D / 8)); [reflexivity| | | |].
all: clear - DR Nlo; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 57%nat kz); [exact EaKL| | | |].
all: clear - Hkz; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 58%nat RZ); [exact EaRZ| | | |].
all: pose proof RZ_facts as (_ & RM & _); clear - RZr RM; first [zlia | replace (2 ^ 5) with 32 by reflexivity; exact RM]. }
split. { apply (AF 59%nat (Uv - 16)); [reflexivity| | | |].
all: pose proof RZ_facts as (_ & RM & _); clear - V1 V2 K32 DR RZr RM; unfold AGis.Uv in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; apply Z.mod_divide in K32 as [q Hq]; [|zlia];
apply Z.mod_divide in RM as [r Hr]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (2 * q + 2 * r - 1); zlia]. }
split. { apply (AF 60%nat Uv); [exact EaU| | | |].
all: pose proof RZ_facts as (_ & RM & _); clear - V1 V2 K32 DR RZr RM; unfold AGis.Uv in *; first [zlia | replace (2 ^ 5) with 32 by reflexivity;
apply Z.mod_divide in K32 as [q Hq]; [|zlia]; apply Z.mod_divide in RM as [r Hr]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q + r); zlia]. }
split. { apply (AF 61%nat SUv); [exact EaSU| | | |].
all: pose proof RZ_facts as (_ & RM & _); clear - DR K32 RM; first [zlia | replace (2 ^ 2) with 4 by reflexivity; apply Z.mod_divide in K32 as [q Hq]; [|zlia]; apply Z.mod_divide in RM as [r Hr]; [|zlia];
apply Z.mod_divide; [zlia|]; unfold AGis.SUv, AGis.SKv, AGis.SHBv in *; exists (536862720 + q + r); rewrite Hq in DR; replace (q * 32) with (q * 4 * 8) in DR by zlia; rewrite Z.div_mul in DR by zlia; zlia]. }
split. { apply (AF 62%nat FILv); [exact EaFIL| | | |].
all: clear - DR; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 63%nat NDv); [exact EaND| | | |].
all: clear - ND2 ND5; first [zlia | replace (2 ^ 3) with 8 by reflexivity; exact ND2]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed of the miss arm.                                                                                        *)
Lemma SEEDM_ok : st_ok tfibsegs E0 MS_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Proof.
assert (RG : regs_ok E0 REGS_G regsU) by (eapply AGj0.REGS_ok; eassumption).
rewrite restrict_mkst_fx. unfold MS_1, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact RG|]. split; [|exact FACTSM_ok].
split; [vm_compute; reflexivity|]. split; [exact REGM_ok | exact PAIRSM_ok].
Qed.
End e.
End d.
