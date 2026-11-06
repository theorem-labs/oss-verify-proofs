(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 790 of its 877 lines of code are new or changed and 844 lines of the source are left out. *)
(* Segment `read` of case 1 of the B walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (op & 3 = 1,
   fuzz/fuzz_boxreg.c:312-373): from the cut C1_I1 (0x80484, listing offset C1_P1 = 0x4d8) to the cut C1_I2 (0x806d4,
   C1_P2 = 0x728), the statement C1_SEG_read of BoxBLxCase1Defs.v.

   The code:
   - 0x80484 .. 0x80490: a1 = s7 & 4 (full), a0 = s1 + 0x88 (the cursor `in`), a2 = the word at sp1 + 0x68 (mac =
     F + 32), `jal read_mac` (0x81618). The run (state c1r_ss1: the slot 0x68 as an atom) stops at the call; read_mac
     is taken from lx_hyps' lh_read_mac (BoxBReadMac.v, caller-journal form): the cursor's 16 bytes are the
     function's stack window (c1r_stack_win, their shadow AR's zero-shadow law: c1r_stk_ra), mac's 6 bytes are its
     side-stack frame (afobj and the frame case of awr_byte; mac's shadow byte is LSH_iter's 6), read_mac.base
     (A_OBJ 6) from BLxLib (c1r_mbase: the read-only bytes, the shadow cells of the const law, img_shadow_vis).
     Its post extends the cut's journal (same count k) and keeps every byte the cut speaks about but the cursor and
     mac (c1r_call_keep).
   - 0x80494 .. 0x806d4: the inlined fuzz_u8 for nch. With no byte left (c1r_after0, state c1r_ss3) `beqz` goes to
     0x806d0 and stores nch = 0; with a byte left (c1r_after1, state c1r_ss2: p, n and the byte as atoms 32 .. 34)
     the cursor advances, the byte is stored at sp1 + 0x50, and the run reaches 0x806d4.
   The branches to the runtime's bodies, each not taken:
   - 0x804ac bgeu s3, a1 -> 0x80fac (UBSan unimp): s3 = 1 and p + 1 with p >= 4096 (c1r_facts2: atoms 19 and 32;
     the engine decides it in c1r_after1's run);
   - 0x804c0 bnez (the shadow byte of p) -> 0x80d9c (__asan_report_load1): the engine's shadow token over the
     shadow entry of the input block (c1r_SH2, c1r_shent_block: AR's block law).
   read_mac's own traps are refuted by its contract's premises (above).
   At 0x806d4 the cut's facts are carried by the runs' frame_of and read_mac's tbcj_kept over every byte outside
   the cursor, sp1 + 0x50 and mac (c1r_out, c1r_carry); the MAC is tbread_mac_out (op & 4) (the input after the
   cursor), six bytes by lxc1_mac_len. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReadMac.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Definition C1R_SB : Z := 0x7fff8000.
Definition c1r_Bx : sv := SOff 18 0.
Definition c1r_span : Z * Z := (C1R_SB, C1R_SB + 2 ^ 44 - 1).
Definition C1R_SPLO : Z := 0x7fff7f800000.
Definition c1r_r68 : YP09.region := YP09.mkRegion (Some 9%nat) 0x68 0x70 0 0 [YP09.mkChunk 0x68 (CVal 8 (SOff 32 0))].
Definition c1r_facts1 : facts := mkFacts [(9%nat, mkAF C1R_SPLO (2 ^ 47) 5); (23%nat, mkAF 0 255 0)] [] [].
Definition c1r_ss1 : sstate := mkSS C1_P1 sr_atoms [c1r_r68] None c1r_facts1.
Definition c1r_cur : YP09.region := YP09.mkRegion (Some 9%nat) 0x88 0x98 0x88 0x98
  [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 33 0))].
Definition c1r_w50 : YP09.region := YP09.mkRegion (Some 9%nat) 0x50 0x58 0x50 0x58 [].
Definition c1r_in : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition c1r_facts2 : facts :=
  mkFacts [(9%nat, mkAF C1R_SPLO (2 ^ 47) 5); (18%nat, mkAF C1R_SB C1R_SB 0); (19%nat, mkAF 1 1 0);
           (32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 1 (2 ^ 26) 0); (34%nat, mkAF 0 255 0)] [] [].
Definition c1r_ss2 : sstate := mkSS 0x4e8 sr_atoms [c1r_cur; c1r_w50; c1r_in] None c1r_facts2.
Definition c1r_SH2 : list shent := [mkSHE 32 0 1].
Definition c1r_cur0 : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x98 0 0 [YP09.mkChunk 0x90 (CVal 8 (SLit 0))].
Definition c1r_facts3 : facts := mkFacts [(9%nat, mkAF C1R_SPLO (2 ^ 47) 5)] [] [].
Definition c1r_ss3 : sstate := mkSS 0x4e8 sr_atoms [c1r_cur0; c1r_w50] None c1r_facts3.

Lemma c1r_div8 : forall a c, a mod 8 = 0 -> 0 <= c < 8 -> (a + c) / 8 = a / 8.
Proof.
intros a c Ha Hc. pose proof (Z.div_mod a 8 ltac:(lia)) as D.
symmetry. apply (Z.div_unique (a + c) 8 (a / 8) c); lia.
Qed.

Lemma c1r_mod8 : forall a c, a mod 8 = 0 -> 0 <= c < 8 -> (a + c) mod 8 = c.
Proof.
intros a c Ha Hc. pose proof (Z.div_mod a 8 ltac:(lia)) as D.
symmetry. apply (Z.mod_unique (a + c) 8 (a / 8) c); lia.
Qed.

Lemma c1r_used : forall full n, 0 <= n -> 0 <= tbread_mac_used full n <= n.
Proof. intros full n Hn. unfold tbread_mac_used. destruct (full =? 0); lia. Qed.

Lemma c1r_den : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma c1r_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma c1r_den_and4 : forall E v, ew E 23 = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_AND (SOff 23 0) (SLit 4)) = Z_to_bv 64 (Z.land v 4).
Proof.
intros E v H Hv. rewrite denot_lit_U. f_equal.
rewrite U_and_lit by lia. rewrite (U_atom E 23 v H) by lia. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

Lemma c1r_val_mem1 : forall (W : world SEGS) mem a v, aview SEGS (w_H W) mem a = Some v ->
  val_mem SEGS (mrestrict (w_H W) mem) a 1 v /\ 0 <= v < 256.
Proof.
  intros W mem a v H. unfold aview in H.
  destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b|] eqn:Hm; [|discriminate H].
  cbn [option_map] in H. injection H as <-.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  intros kk Hk. assert (kk = 0%nat) by lia. subst kk. replace (a + Z.of_nat 0) with a by lia. rewrite Hm. f_equal.
  rewrite le_byte_small by (cbn; lia). replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma c1r_garr8_view : forall (W : world SEGS) mem p (l : list byte) j,
  garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) l) -> 0 <= j < Z.of_nat (length l) ->
  aview SEGS (w_H W) mem (p + j) = Some (bv_unsigned (nth (Z.to_nat j) l (Z_to_bv 8 0))).
Proof.
  intros W mem p l j Hg Hj. destruct (Hg (Z.to_nat j) ltac:(rewrite length_map; lia)) as [Hv Hb].
  rewrite Z2Nat.id in Hv by lia.
  assert (E : nth (Z.to_nat j) (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth (Z.to_nat j) l (Z_to_bv 8 0))).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0 : byte))) by (rewrite length_map; lia). apply map_nth. }
  rewrite E in Hv, Hb. apply aview_of_val_mem1; assumption.
Qed.

Lemma c1r_reg_pi : forall E ss H ms (x : bv 5) n v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) x = SOff n 0 -> ew E n = v -> getr (ms_regs ms) x = v.
Proof.
intros E ss H ms x n v HS Hq Hn. rewrite (st_ok_pi_restrict_reg H E ss ms x HS), Hq.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hn.
Qed.

Lemma c1r_shape : forall pc (W : world SEGS) ms,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  restrict (w_H W) ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS).
Proof.
intros pc W ms Hpc Hresv Hpend Hrom Hfregs Hfcsr.
destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
subst. reflexivity.
Qed.

Lemma c1r_rd_eq : forall (H : word -> bool) m m' a v,
  (forall j, 0 <= j < 8 -> aview SEGS H m' (a + j) = aview SEGS H m (a + j)) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H m') a = Some v.
Proof.
  intros H m m' a v K Hr.
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.


Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Section d.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* The machine stack's shadow is zero (AR's zero-shadow law over the layout's stack range). *)
Lemma c1r_stk_ra : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
  ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros ly S W mem md a n HAR Hlo Hhi x Hx.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5, T6.
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    (or_introl eq_refl)) as Z0.
  cbn [fst snd] in Z0.
  exists 0. split; [|left; reflexivity].
  pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as D1.
  pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as D2.
  pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
  rewrite T5, Z.add_0_r in D1. rewrite T6, Z.add_0_r in D2.
  set (ql := ly_stk_lo ly / 4096) in *. set (qh := ly_stk_hi ly / 4096) in *.
  assert (E1 : ly_stk_lo ly / 8 = 512 * ql) by (rewrite D1; replace (4096 * ql) with ((512 * ql) * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (ly_stk_hi ly - ly_stk_lo ly) / 8 = 512 * (qh - ql))
    by (rewrite D1, D2; replace (4096 * qh - 4096 * ql) with ((512 * (qh - ql)) * 8) by lia; apply Z.div_mul; lia).
  specialize (Z0 (x / 8 - 512 * ql)). rewrite E2 in Z0.
  unfold shadow_of_addr in Z0 |- *. rewrite E1 in Z0.
  replace (SHADOW_OFF + 512 * ql + (x / 8 - 512 * ql)) with (SHADOW_OFF + x / 8) in Z0 by lia.
  apply Z0. lia.
Qed.

(* A byte of the caller's stack window: the caller's journal may let a callee write it. *)
Lemma c1r_stack_win : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= a < sp0 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a /\
  ~ aowned B lyc Sc a /\ ly_stk_lo lyc <= a < ly_stk_hi lyc.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Ha.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hs : ly_stk_lo lyc <= a < ly_stk_hi lyc) by lia.
  split; [left; exact Ha|]. split; [exact (Hpres a Ha)|]. split; [|exact Hs].
  exact (al_stack _ _ LAWS lyc Sc W memc mdc a HAR Hs).
Qed.

(* A heap block's bytes as a shadow entry of the token engine, against any shadow-base term Bx. *)
Lemma c1r_shent_block : forall lyb Sb (Wb : world SEGS) memb mdb Bx Ex (qa b sz lo hi : Z) (n : nat),
  AR SEGS B lyb Sb Wb memb mdb -> In (b, sz) (ablocks B lyb Sb) ->
  U Ex Bx = SHADOW_OFF -> U Ex (SOff n 0) = qa ->
  b <= qa + lo -> lo <= hi -> qa + hi <= b + req_size sz ->
  shent_ok SEGS Bx Ex (mrestrict (w_H Wb) memb) (mkSHE n lo hi).
Proof.
  intros lyb Sb Wb memb mdb Bx Ex qa b sz lo hi n HAR Hin HBx Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyb Sb Wb memb mdb b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS lyb Sb Wb memb mdb b sz (qa + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

(* read_mac.base (A_OBJ 6): its five bytes from the read-only image, its shadow from AR's const law (BLxLib). *)
Lemma c1r_mbase : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (forall j, 0 <= j < 5 -> aview SEGS (w_H W) mem (VAL (A_OBJ 6) + j) =
     Some (bv_unsigned (nth (Z.to_nat j) tbread_mac_base (Z_to_bv 8 0)))) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 6)) 5 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 6)) 5.
Proof.
intros ly S W mem md HAR HRO.
pose proof (lh_glob B MT HY) as GL.
assert (Hg : In (6%nat, 5) LX_GLOBS) by (unfold LX_GLOBS; cbn [In]; tauto).
pose proof (blx_al _ GL _ Hg) as Hal. pose proof (blx_marg _ GL _ Hg) as Hmg. cbn [fst snd] in Hal, Hmg.
pose proof (lx_rom_viewN B W mem HRO) as HRVN.
pose proof (blx_rom_bytes _ GL (6%nat, [0; 64; 171; 0; 0]) ltac:(unfold LX_GLOB_BYTES; cbn [In]; tauto)) as Hrb.
cbn [fst snd] in Hrb.
split.
{ intros j Hj. destruct (Hrb j ltac:(cbn; lia)) as (Hrom & Ho & He & Hv).
  rewrite (HRVN _ Hrom Ho He), Hv. f_equal.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity. }
pose proof HAR as (M & _).
pose proof (am_const _ _ _ _ M) as C.
assert (Hin : In (z1 (ANum (shadow_addr (VAL (A_OBJ 6)))) 5) (as_const B ly)).
{ apply (blx_cells _ GL ly). unfold lx_glob_cells. apply in_flat_map. exists (6%nat, 5). split; [exact Hg|].
  cbn [fst snd]. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) C _ Hin) as Hc. unfold cell_holds in Hc.
cbn [c_at c_val c_w z1 c1 aeval] in Hc.
pose proof (Hc 0%nat ltac:(lia)) as Hc0. cbn [Z.of_nat] in Hc0. rewrite Z.add_0_r in Hc0.
replace (le_byte 5 1 0) with 5 in Hc0 by reflexivity.
set (x := VAL (A_OBJ 6)) in *.
assert (Hx8 : x mod 8 = 0).
{ pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D. rewrite D.
  replace (32 * (x / 32)) with ((4 * (x / 32)) * 8) by lia. apply Z_mod_mult. }
split.
{ intros y Hy. exists 5. split.
  - unfold shadow_of_addr. replace y with (x + (y - x)) by lia. rewrite (c1r_div8 x (y - x) Hx8) by lia.
    unfold shadow_addr in Hc0. exact Hc0.
  - right. split; [|lia]. replace y with (x + (y - x)) by lia. rewrite (c1r_mod8 x (y - x) Hx8) by lia. lia. }
intros s Hs.
pose proof (blx_isv _ GL) as ISV.
assert (Ha : shadow_addr ((s - SHADOW_OFF) * 8) = s) by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
rewrite <- Ha. apply (ISV ly S W mem md); [exact HAR|].
unfold shadow_addr in Hs.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D1b.
pose proof (Z.div_mod (x + 5 - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + 5 - 1) 8 ltac:(lia)) as D2b.
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D3b.
pose proof (Z.div_mod (SHADOW_OFF + (x + 5 - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + 5 - 1) / 8) 8 ltac:(lia)) as D4b.
lia.
Qed.

Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Hypothesis HNEXT : lx_from B MT POST (C1_I2 B MT i).
Variables (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model).
Variables (q : nat) (r fab op : Z) (bs : list byte).
Hypothesis HB : lx_base B MT cx.
Hypothesis HJ : ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
  [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
Hypothesis HC1 : c1_body B MT i cx fp C1_P1 k acc ly3 S3 W3 ms3 r fab bs q.
Hypothesis Hop : 0 <= op < 256.
Hypothesis R19 : getr (ms_regs ms3) 19 = w64 1.
Hypothesis R23 : getr (ms_regs ms3) 23 = w64 op.

#[local] Notation sp0 := (lsp0 cx).
#[local] Notation sp1 := (lsp1 cx).
#[local] Notation FF := (lF cx fp).
#[local] Notation SHF := (lSH cx fp).

Lemma c1r_geo :
  sp0 mod 16 = 0 /\ alloc_ceiling + 32768 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 - 287 <= sp1 <= sp0 - 256 /\
  sp1 mod 32 = 0 /\
  4096 <= FF /\ FF + 512 <= alloc_ceiling /\ in_app FF 512 /\ FF mod 64 = 0 /\ SHF = SHADOW_OFF + FF / 8 /\
  frame_addr ly3 LX_CID fp = FF /\ In (LX_CID, fp) (frames S3) /\
  In (r, LX_REG) (ablocks B ly3 S3) /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= FF \/ FF + 512 <= r).
Proof.
pose proof (lx_sp_facts B MT cx HB) as (H1 & H2 & H3 & H4 & H5).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (F1 & F2 & F3 & _ & F5 & F6).
pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
pose proof HC1 as (_ & _ & _ & _ & HBLK & _).
pose proof HJ as (HAR3 & _).
assert (Hin : In (r, LX_REG) (ablocks B ly3 S3))
  by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hin) as (_ & Hr4096 & Hrc & _).
change (req_size LX_REG) with 288 in Hrc.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ r LX_REG LX_CID fp HAR3 Hin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (req_size LX_REG) with 288 in Hsep.
rewrite EF in Hsep. assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity). rewrite Hfb in Hsep.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F5|]. split; [exact F6|].
split; [exact EF|]. split; [exact Hfin|]. split; [exact Hin|]. split; [exact Hr4096|]. split; [exact Hrc|]. exact Hsep.
Qed.

Lemma c1r_inblk : 0 < lc_n cx ->
  In (lc_p cx, lc_n cx) (ablocks B ly3 S3) /\ 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling /\
  lc_n cx < 2 ^ 26 /\ (lc_p cx + lc_n cx <= FF \/ FF + 512 <= lc_p cx).
Proof.
intros Hn.
pose proof HC1 as (_ & _ & _ & _ & HBLK & _).
pose proof HB as (_ & _ & _ & Hpn & _).
pose proof HJ as (HAR3 & _).
destruct Hpn as [Hn0 | ((_ & Hn26) & Hinc)]; [lia|].
assert (Hin : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
  by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; left; exact Hinc).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4096 & Hpc & _).
assert (Hrq : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
rewrite Hrq in Hpc.
assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ LX_CID fp HAR3 Hin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Hrq in Hsep.
rewrite (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) in Hsep.
assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity). rewrite Hfb in Hsep.
split; [exact Hin|]. split; [exact Hp4096|]. split; [exact Hpc|]. split; [exact Hn26 | exact Hsep].
Qed.

(* The bytes of the cut's facts that this walk does not write: the cursor, the width byte's slot and mac. *)
Definition c1r_out (a : Z) : Prop :=
  (sp1 <= a < 2 ^ 64 \/ lc_p cx <= a < lc_p cx + lc_n cx \/ FF <= a < FF + 512 \/ SHF <= a < SHF + 64 \/
   r <= a < r + 288) /\
  ~ (sp1 + 0x50 <= a < sp1 + 0x58) /\ ~ (sp1 + 0x88 <= a < sp1 + 0x98) /\ ~ (FF + 32 <= a < FF + 38).

Lemma c1r_out_range : forall a, c1r_out a -> 0 <= a < 2 ^ 64.
Proof.
intros a (Ha & _).
pose proof c1r_geo as (_ & G2 & G3 & G4 & _ & G6 & G7 & _ & _ & G10 & _ & _ & _ & G14 & G15 & _).
pose proof asan_consts as (C1 & _).
assert (Hd0 : 0 <= FF / 8) by (apply Z.div_pos; lia).
assert (Hd1 : FF / 8 <= FF) by (apply Z.div_le_upper_bound; lia).
rewrite G10 in Ha. unfold SHADOW_OFF in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; try lia.
destruct (Z_lt_le_dec 0 (lc_n cx)) as [Hn|Hn]; [|lia].
pose proof (c1r_inblk Hn) as (_ & P1 & P2 & _). lia.
Qed.

Lemma c1r_out_stk : forall a, sp1 <= a < sp1 + 0x50 \/ sp1 + 0x58 <= a < sp1 + 0x88 \/ sp1 + 0x98 <= a < 2 ^ 64 ->
  c1r_out a.
Proof.
intros a Ha. pose proof c1r_geo as (_ & G2 & G3 & G4 & _ & G6 & G7 & _).
unfold c1r_out. split; [left; lia|]. split; [lia|]. split; lia.
Qed.

Lemma c1r_out_frame : forall a, FF <= a < FF + 512 -> ~ (FF + 32 <= a < FF + 38) -> c1r_out a.
Proof.
intros a Ha Hm. pose proof c1r_geo as (_ & G2 & G3 & G4 & _ & G6 & G7 & _).
unfold c1r_out. split; [right; right; left; lia|]. split; [lia|]. split; lia.
Qed.

Lemma c1r_out_sh : forall a, SHF <= a < SHF + 64 -> c1r_out a.
Proof.
intros a Ha. pose proof c1r_geo as (_ & G2 & G3 & G4 & _ & G6 & G7 & G8 & _ & G10 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod FF 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as Dm.
unfold c1r_out. rewrite G10 in Ha |- *.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
split; [right; right; right; left; lia|]. split; [lia|]. split; lia.
Qed.

Lemma c1r_out_in : forall a, lc_p cx <= a < lc_p cx + lc_n cx -> c1r_out a.
Proof.
intros a Ha. destruct (Z_lt_le_dec 0 (lc_n cx)) as [Hn|Hn]; [|lia].
pose proof (c1r_inblk Hn) as (_ & P1 & P2 & _ & P5).
pose proof c1r_geo as (_ & G2 & G3 & G4 & _).
unfold c1r_out. split; [right; left; lia|]. split; [lia|]. split; lia.
Qed.

Lemma c1r_out_reg : forall a, r <= a < r + 288 -> c1r_out a.
Proof.
intros a Ha. pose proof c1r_geo as (_ & G2 & G3 & G4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G14 & G15 & G16).
unfold c1r_out. split; [right; right; right; right; lia|]. split; [lia|]. split; lia.
Qed.

Lemma c1r_rd_keep : forall m m' a v,
  (forall x, c1r_out x -> aview SEGS (w_H W3) m' x = aview SEGS (w_H W3) m x) ->
  (forall j, 0 <= j < 8 -> c1r_out (a + j)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
intros m m' a v KP Ho. apply c1r_rd_eq. intros j Hj. apply KP. apply Ho. exact Hj.
Qed.

(* The cut's facts at the end of the segment, from the bytes the segment does not write. *)
Lemma c1r_carry : forall (msf : machine_state) (q3 : nat),
  msf = mkst (ms_regs msf) (Z_to_bv 64 (BASE + C1_P2)) (ms_mem msf) (seg_rom SEGS) ->
  lregs cx fp msf -> getr (ms_regs msf) 20 = w64 r -> getr (ms_regs msf) 21 = w64 (FF + 64) ->
  (forall a, c1r_out a -> aview SEGS (w_H W3) (ms_mem msf) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  lcur cx W3 msf q3 ->
  c1_body B MT i cx fp C1_P2 k acc ly3 S3 W3 msf r fab bs q3.
Proof.
intros msf q3 Hsh HRG H20 H21 KP HCUR3.
pose proof HC1 as (HBODY & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPREV & _ & HSLL & S58 & S48 & _ & _).
pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof c1r_geo as (_ & G2 & G3 & G4 & _).
assert (SLK : forall off v, (0 <= off /\ off + 8 <= 0x50) \/ (0x58 <= off /\ off + 8 <= 0x88) ->
  lslot cx W3 ms3 off v -> lslot cx W3 msf off v).
{ intros off v Hoff Hv. unfold lslot, lview in *. apply (c1r_rd_keep (ms_mem ms3) (ms_mem msf) _ _ KP); [|exact Hv].
  intros j Hj. apply c1r_out_stk. lia. }
assert (Hpc : ms_pc_val msf = w64 (BASE + C1_P2)) by (rewrite Hsh; reflexivity).
assert (Hrv : ms_resv msf = None) by (rewrite Hsh; reflexivity).
assert (Hsv : ms_svc_pending msf = None) by (rewrite Hsh; reflexivity).
assert (Hrm : ms_rom msf = seg_rom SEGS) by (rewrite Hsh; reflexivity).
assert (Hfr : ms_fregs msf = fp_regs) by (rewrite Hsh; reflexivity).
assert (Hfc : ms_fcsr msf = fp_csr) by (rewrite Hsh; reflexivity).
assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
split.
{ split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hrm|].
  split; [exact Hfr|]. split; [exact Hfc|]. split; [exact HRG|].
  split.
  { destruct HSAVED as (Hra & Hsj). split.
    - unfold lview in *. apply (c1r_rd_keep _ _ _ _ KP); [intros j Hj; apply c1r_out_stk; lia | exact Hra].
    - intros j Hj. unfold lview in *. apply (c1r_rd_keep _ _ _ _ KP); [intros j' Hj'; apply c1r_out_stk; lia | exact (Hsj j Hj)]. }
  split.
  { intros j Hj. unfold lview. rewrite KP; [exact (HSH j Hj)|]. apply c1r_out_sh.
    change (length LSH_iter) with 52%nat in Hj. lia. }
  split.
  { unfold lview in *. rewrite Hfb in *.
    apply (c1r_rd_keep _ _ _ _ KP); [intros j Hj; apply c1r_out_frame; lia | exact HFLAG]. }
  split; [apply (SLK 0x10); [lia | exact HS10]|].
  split; [apply (SLK 0x18); [lia | exact HS18]|].
  split; [apply (SLK 0x80); [lia | exact HS80]|].
  intros j Hj. destruct (HINP j Hj) as [Hv Hb]. split; [|exact Hb].
  intros kk Hkk. assert (kk = 0)%nat by lia. subst kk.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
  rewrite length_map in Hj.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msf) _
             (KP (lc_p cx + Z.of_nat j) ltac:(apply c1r_out_in; unfold lc_n; lia))).
  exact Hv0. }
split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
split.
{ intros j Hj. unfold lview. rewrite KP; [exact (HREG j Hj)|]. apply c1r_out_reg. unfold LX_REG in Hj. lia. }
split; [exact HINV|]. split; [exact HFAB|].
split.
{ intros j Hj. unfold lview. rewrite KP; [exact (HPREV j Hj)|]. unfold LX_REG in Hj. apply c1r_out_frame; lia. }
split; [exact HCUR3|].
split.
{ destruct HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
  split; [apply (SLK 0x08); [lia | exact L08]|]. split; [apply (SLK 0x28); [lia | exact L28]|].
  split; [apply (SLK 0x30); [lia | exact L30]|]. split; [apply (SLK 0x38); [lia | exact L38]|].
  split; [apply (SLK 0x40); [lia | exact L40]|]. split; [apply (SLK 0x68); [lia | exact L68]|].
  split; [apply (SLK 0x70); [lia | exact L70]|]. apply (SLK 0x78); [lia | exact L78]. }
split; [apply (SLK 0x58); [lia | exact S58]|].
split; [apply (SLK 0x48); [lia | exact S48]|].
split; [exact H20 | exact H21].
Qed.

(* read_mac's tbcj_kept: every byte the cut's facts read, outside the cursor and mac, is kept. *)
Lemma c1r_call_keep : forall memT mem2,
  tbcj_kept B READ_MAC_STKB ly3 S3 W3 memT W3 mem2 sp1
    (fun a => sp1 + 0x88 <= a < sp1 + 0x88 + 16 \/ FF + 32 <= a < FF + 32 + 6) ->
  forall a, c1r_out a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a.
Proof.
intros memT mem2 (K1 & K2 & _ & K4 & _) a (Ha & N50 & N88 & Nmac).
pose proof c1r_geo as (_ & G2 & G3 & G4 & _ & G6 & G7 & _ & _ & G10 & EF & Hfin & Hrin & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : READ_MAC_STKB = 4128) by reflexivity.
assert (NE : ~ (sp1 + 0x88 <= a < sp1 + 0x88 + 16 \/ FF + 32 <= a < FF + 32 + 6)) by lia.
assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- apply K1; [lia | rewrite HSTK; lia | exact NE].
- destruct (Z_lt_le_dec 0 (lc_n cx)) as [Hn|Hn]; [|lia].
  pose proof (c1r_inblk Hn) as (Hin & _).
  pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq].
  replace a with (lc_p cx + (a - lc_p cx)) in NE |- * by lia.
  apply (K2 (lc_p cx) (lc_n cx) (a - lc_p cx) Hin); [lia | exact NE].
- apply (K4 LX_CID fp a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF, Hfb; lia | exact NE].
- apply (K4 LX_CID fp a Hfin); [|exact NE]. right. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb.
  change (512 / 8) with 64. change (shadow_addr (lF cx fp)) with (lSH cx fp). lia.
- replace a with (r + (a - r)) in NE |- * by lia.
  apply (K2 r LX_REG (a - r) Hrin); [change (req_size LX_REG) with 288; lia | exact NE].
Qed.

Lemma c1r_after1 : forall regs2 mem2 md2 (q2 : nat) (M : list byte),
  ajournal SEGS B LX_STK sp0 [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k ->
  aregs_preserved (ms_regs ms3) regs2 ->
  (forall a, c1r_out a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) mem2 (FF + 32 + j) = Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  (q2 < length (lc_pl cx))%nat ->
  rdword (aview SEGS (w_H W3) mem2) (sp1 + 0x88) = Some (lc_p cx + Z.of_nat q2) ->
  rdword (aview SEGS (w_H W3) mem2) (sp1 + 0x90) = Some (lc_n cx - Z.of_nat q2) ->
  SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x4e8)) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
intros regs2 mem2 md2 q2 M HJ2 HP KP HML HMAC Hq2 C88 C90.
pose proof c1r_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & EF & Hfin & Hrin & G14 & G15 & G16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC1 as (HBODY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G20 & G21).
pose proof HBODY as (_ & _ & _ & _ & _ & _ & HREGS & _ & _ & _ & _ & _ & _ & HINP).
pose proof HREGS as (L2 & L8 & L9 & L3 & L4 & L18 & L22).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hn : 0 < lc_n cx) by (unfold lc_n; lia).
pose proof (c1r_inblk Hn) as (Hinb & P1 & P2 & P3 & P4).
assert (HBY : aview SEGS (w_H W3) mem2 (lc_p cx + Z.of_nat q2) = Some (bv_unsigned (nth q2 (lc_pl cx) (Z_to_bv 8 0)))).
{ rewrite KP by (apply c1r_out_in; unfold lc_n; lia).
  pose proof (c1r_garr8_view W3 (ms_mem ms3) (lc_p cx) (lc_pl cx) (Z.of_nat q2) HINP ltac:(lia)) as Hv.
  rewrite Nat2Z.id in Hv. exact Hv. }
pose proof (c1r_val_mem1 W3 mem2 _ _ HBY) as (HBYv & HBYr).
remember (Eimg (Ereg regs2 [w64 (lc_p cx + Z.of_nat q2); w64 (lc_n cx - Z.of_nat q2);
  w64 (bv_unsigned (nth q2 (lc_pl cx) (Z_to_bv 8 0)))])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (ER : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr regs2 x)
  by (intros n x Hx; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hx).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [w64 (lc_p cx + Z.of_nat q2); w64 (lc_n cx - Z.of_nat q2);
  w64 (bv_unsigned (nth q2 (lc_pl cx) (Z_to_bv 8 0)))] (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (ER 2%nat (Z_to_bv 5 2) eq_refl), (HP 2) by (unfold acallee_saved; lia); exact L2).
assert (E8 : ew E 8 = w64 sp0) by (rewrite (ER 8%nat (Z_to_bv 5 8) eq_refl), (HP 8) by (unfold acallee_saved; lia); exact L8).
assert (E9 : ew E 9 = w64 sp1) by (rewrite (ER 9%nat (Z_to_bv 5 9) eq_refl), (HP 9) by (unfold acallee_saved; lia); exact L9).
assert (E3 : ew E 3 = getr (lc_regs cx) 3) by (rewrite (ER 3%nat (Z_to_bv 5 3) eq_refl), (HP 3) by (unfold acallee_saved; lia); exact L3).
assert (E4 : ew E 4 = getr (lc_regs cx) 4) by (rewrite (ER 4%nat (Z_to_bv 5 4) eq_refl), (HP 4) by (unfold acallee_saved; lia); exact L4).
assert (E18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (ER 18%nat (Z_to_bv 5 18) eq_refl), (HP 18) by (unfold acallee_saved; lia); exact L18).
assert (E19 : ew E 19 = w64 1) by (rewrite (ER 19%nat (Z_to_bv 5 19) eq_refl), (HP 19) by (unfold acallee_saved; lia); exact R19).
assert (E20 : ew E 20 = w64 r) by (rewrite (ER 20%nat (Z_to_bv 5 20) eq_refl), (HP 20) by (unfold acallee_saved; lia); exact G20).
assert (E21 : ew E 21 = w64 (FF + 64)) by (rewrite (ER 21%nat (Z_to_bv 5 21) eq_refl), (HP 21) by (unfold acallee_saved; lia); exact G21).
assert (E22 : ew E 22 = w64 SHF) by (rewrite (ER 22%nat (Z_to_bv 5 22) eq_refl), (HP 22) by (unfold acallee_saved; lia); exact L22).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth] in E32, E33, E34.
clear ER EX.
pose proof (c1_rdword_range _ _ _ _ C88) as Rp. pose proof (c1_rdword_range _ _ _ _ C90) as Rn.
assert (HS : st_ok_pi SEGS VAL E c1r_ss2 (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 0x4e8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold c1r_ss2. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, c1r_cur. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia.
      * repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ _ 136 8 (SOff 32 0) (lc_p cx + Z.of_nat q2)); [exact (c1r_den E 32 _ E32) | cbn; lia | cbn; lia |].
           exact (val_mem_of_rdword SEGS (w_H W3) mem2 _ _ C88).
        -- apply (chunk_ok_val SEGS E _ _ 144 8 (SOff 33 0) (lc_n cx - Z.of_nat q2)); [exact (c1r_den E 33 _ E33) | cbn; lia | cbn; lia |].
           exact (val_mem_of_rdword SEGS (w_H W3) mem2 _ _ C90).
    + unfold region_ok, c1r_w50. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia.
    + unfold region_ok, c1r_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E32, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 34 0) (bv_unsigned (nth q2 (lc_pl cx) (Z_to_bv 8 0)))); [exact (c1r_den E 34 _ E34) | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact HBYv.
  - apply pairwise_disjoint_of_extents. unfold c1r_cur, c1r_w50, c1r_in, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; exact I].
    cbn [c1r_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E18, E19, E32, E33, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold C1R_SPLO, C1R_SB, SHADOW_OFF.
    assert (Hq2' : Z.of_nat q2 < lc_n cx) by (unfold lc_n; lia).
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }

assert (SHOK : sh_ok SEGS c1r_Bx c1r_SH2 E (mrestrict (w_H W3) mem2)).
{ unfold sh_ok, c1r_SH2. apply Forall_cons; [|apply Forall_nil].
  apply (c1r_shent_block _ _ _ _ _ c1r_Bx E (lc_p cx + Z.of_nat q2) (lc_p cx) (lc_n cx) 0 1 32 HAR2 Hinb).
  - unfold c1r_Bx. apply (U_atom E 18 SHADOW_OFF E18). unfold SHADOW_OFF; lia.
  - apply (U_atom E 32 _ E32). lia.
  - lia.
  - lia.
  - pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. unfold lc_n in *. lia. }
paj_run_to_tok RUNTO HS HJ2 SHOK c1r_span C1_P2.
{ unfold c1r_ss2, c1r_cur, c1r_w50, c1r_in. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [reflexivity | rewrite E9, unsigned_lit_small by lia; lia | cbn; unfold LX_STK; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [reflexivity | rewrite E9, unsigned_lit_small by lia; lia | cbn; unfold LX_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }

pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ ms HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
change (BASE + 1832) with (BASE + C1_P2) in Hshape.
assert (EW : forall n, (n < 512)%nat -> ew (ewset (ewset E 512 w) 513 w0) n = ew E n)
  by (intros n Hn'; rewrite !ew_ewset_other by lia; reflexivity).
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 0x88 <= a < sp1 + 0x98 \/ sp1 + 0x50 <= a < sp1 + 0x58) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hna.
  apply (kept_of_frame E (ss_mem c1r_ss2) (w_H W3) mem2 (ms_mem ms)
           (fun x => sp1 + 0x88 <= x < sp1 + 0x98 \/ sp1 + 0x50 <= x < sp1 + 0x58) HFr); [|exact Ha|exact Hna].
  intros bb wlo whi aa Hwin Hr.
  change (windows (ss_mem c1r_ss2)) with [(Some 9%nat, 136, 152); (Some 9%nat, 80, 88); (Some 32%nat, 0, 0)] in Hwin.
  cbn [In] in Hwin.
  destruct Hwin as [Hw | [Hw | [Hw | []]]]; injection Hw as <- <- <-; cbn [base_val] in Hr; [| |lia];
    rewrite E9, unsigned_lit_small in Hr by lia; lia. }

assert (F2 : getr (ms_regs ms) 2 = w64 sp1) by (eapply (c1r_reg_pi _ _ _ _ _ 2%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E2]).
assert (F8 : getr (ms_regs ms) 8 = w64 sp0) by (eapply (c1r_reg_pi _ _ _ _ _ 8%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E8]).
assert (F9 : getr (ms_regs ms) 9 = w64 sp1) by (eapply (c1r_reg_pi _ _ _ _ _ 9%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E9]).
assert (F3 : getr (ms_regs ms) 3 = getr (lc_regs cx) 3) by (eapply (c1r_reg_pi _ _ _ _ _ 3%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E3]).
assert (F4 : getr (ms_regs ms) 4 = getr (lc_regs cx) 4) by (eapply (c1r_reg_pi _ _ _ _ _ 4%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E4]).
assert (F18 : getr (ms_regs ms) 18 = w64 SHADOW_OFF) by (eapply (c1r_reg_pi _ _ _ _ _ 18%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E18]).
assert (F20 : getr (ms_regs ms) 20 = w64 r) by (eapply (c1r_reg_pi _ _ _ _ _ 20%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E20]).
assert (F21 : getr (ms_regs ms) 21 = w64 (FF + 64)) by (eapply (c1r_reg_pi _ _ _ _ _ 21%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E21]).
assert (F22 : getr (ms_regs ms) 22 = w64 SHF) by (eapply (c1r_reg_pi _ _ _ _ _ 22%nat _ HS); [vm_compute; reflexivity | rewrite EW by lia; exact E22]).
assert (S88f : lslot cx W3 ms 0x88 (lc_p cx + Z.of_nat (S q2))).
{ unfold lslot. eapply (lx_word_of_ss W3 ms _ _ 0%nat); [exact HS | reflexivity | rewrite EW by lia; rewrite E9; apply unsigned_lit_small; lia
  | cbn [In]; left; reflexivity | | ].
  - rewrite (c1r_den_off _ 32 (lc_p cx + Z.of_nat q2) 1) by (rewrite ?EW by lia; first [exact E32 | lia]). unfold w64. f_equal. lia.
  - lia. }

assert (S90f : lslot cx W3 ms 0x90 (lc_n cx - Z.of_nat (S q2))).
{ unfold lslot. eapply (lx_word_of_ss W3 ms _ _ 0%nat); [exact HS | reflexivity | rewrite EW by lia; rewrite E9; apply unsigned_lit_small; lia
  | cbn [In]; right; left; reflexivity | | ].
  - rewrite (c1r_den_off _ 33 (lc_n cx - Z.of_nat q2) (-1)) by (rewrite ?EW by lia; first [exact E33 | lia]). unfold w64. f_equal. lia.
  - unfold lc_n in *. lia. }
assert (S50f : lslot cx W3 ms 0x50 (bv_unsigned (nth q2 (lc_pl cx) (Z_to_bv 8 0)))).
{ unfold lslot. eapply (lx_word_of_ss W3 ms _ _ 1%nat); [exact HS | reflexivity | rewrite EW by lia; rewrite E9; apply unsigned_lit_small; lia
  | cbn [In]; left; reflexivity | | ].
  - rewrite (c1r_den _ 34 _) by (rewrite EW by lia; exact E34). reflexivity.
  - lia. }
assert (KPF : forall a, c1r_out a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- (KP a Ha). apply KF; [exact (c1r_out_range a Ha)|]. destruct Ha as (_ & N50 & N88 & _). lia. }
apply (HNEXT cx fp k acc ly3 S3 W3 ms _ HB HJ2 HFR HMO).
exists (S q2), r, fab, bs, M, (bv_unsigned (nth q2 (lc_pl cx) (Z_to_bv 8 0))). split.
- apply c1r_carry; [exact Hshape | | exact F20 | exact F21 | exact KPF | ].
  + split; [exact F2|]. split; [exact F8|]. split; [exact F9|]. split; [exact F3|]. split; [exact F4|].
    split; [exact F18 | exact F22].
  + split; [lia|]. split; [exact S88f | exact S90f].
- split; [|split; [exact S50f | exact HBYr]].
  split; [exact HML|]. intros j Hj. unfold lview. rewrite KF; [exact (HMAC j Hj) | lia | lia].
Qed.

Lemma c1r_after0 : forall regs2 mem2 md2 (q2 : nat) (M : list byte),
  ajournal SEGS B LX_STK sp0 [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k ->
  aregs_preserved (ms_regs ms3) regs2 ->
  (forall a, c1r_out a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) mem2 (FF + 32 + j) = Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  q2 = length (lc_pl cx) ->
  rdword (aview SEGS (w_H W3) mem2) (sp1 + 0x88) = Some (lc_p cx + Z.of_nat q2) ->
  rdword (aview SEGS (w_H W3) mem2) (sp1 + 0x90) = Some (lc_n cx - Z.of_nat q2) ->
  SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x4e8)) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
intros regs2 mem2 md2 q2 M HJ2 HP KP HML HMAC Hq2 C88 C90.
pose proof c1r_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & EF & Hfin & Hrin & G14 & G15 & G16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC1 as (HBODY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G20 & G21).
pose proof HBODY as (_ & _ & _ & _ & _ & _ & HREGS & _ & _ & _ & _ & _ & _ & _).
pose proof HREGS as (L2 & L8 & L9 & L3 & L4 & L18 & L22).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hn0 : lc_n cx - Z.of_nat q2 = 0) by (unfold lc_n; subst q2; lia).
rewrite Hn0 in C90.
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (ER : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr regs2 x)
  by (intros n x Hx; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hx).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (ER 2%nat (Z_to_bv 5 2) eq_refl), (HP 2) by (unfold acallee_saved; lia); exact L2).
assert (E8 : ew E 8 = w64 sp0) by (rewrite (ER 8%nat (Z_to_bv 5 8) eq_refl), (HP 8) by (unfold acallee_saved; lia); exact L8).
assert (E9 : ew E 9 = w64 sp1) by (rewrite (ER 9%nat (Z_to_bv 5 9) eq_refl), (HP 9) by (unfold acallee_saved; lia); exact L9).
assert (E3 : ew E 3 = getr (lc_regs cx) 3) by (rewrite (ER 3%nat (Z_to_bv 5 3) eq_refl), (HP 3) by (unfold acallee_saved; lia); exact L3).
assert (E4 : ew E 4 = getr (lc_regs cx) 4) by (rewrite (ER 4%nat (Z_to_bv 5 4) eq_refl), (HP 4) by (unfold acallee_saved; lia); exact L4).
assert (E18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (ER 18%nat (Z_to_bv 5 18) eq_refl), (HP 18) by (unfold acallee_saved; lia); exact L18).
assert (E20 : ew E 20 = w64 r) by (rewrite (ER 20%nat (Z_to_bv 5 20) eq_refl), (HP 20) by (unfold acallee_saved; lia); exact G20).
assert (E21 : ew E 21 = w64 (FF + 64)) by (rewrite (ER 21%nat (Z_to_bv 5 21) eq_refl), (HP 21) by (unfold acallee_saved; lia); exact G21).
assert (E22 : ew E 22 = w64 SHF) by (rewrite (ER 22%nat (Z_to_bv 5 22) eq_refl), (HP 22) by (unfold acallee_saved; lia); exact L22).
clear ER.
assert (HS : st_ok_pi SEGS VAL E c1r_ss3 (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 0x4e8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold c1r_ss3. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, c1r_cur0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 144 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) mem2 _ _ C90).
    + unfold region_ok, c1r_w50. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia.
  - apply pairwise_disjoint_of_extents. unfold c1r_cur0, c1r_w50, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; exact I].
    cbn [c1r_facts3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. unfold C1R_SPLO.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS c1r_Bx [] E (mrestrict (w_H W3) mem2)) by apply Forall_nil.
paj_run_to_tok RUNTO HS HJ2 SHOK c1r_span C1_P2.
{ unfold c1r_ss3, c1r_cur0, c1r_w50. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [reflexivity | rewrite E9, unsigned_lit_small by lia; lia | cbn; unfold LX_STK; lia | cbn; lia |].
  apply awr_ok_nil. }

pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ ms HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
change (BASE + 1832) with (BASE + C1_P2) in Hshape.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 0x50 <= a < sp1 + 0x58) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hna.
  apply (kept_of_frame E (ss_mem c1r_ss3) (w_H W3) mem2 (ms_mem ms) (fun x => sp1 + 0x50 <= x < sp1 + 0x58) HFr);
    [|exact Ha|exact Hna].
  intros bb wlo whi aa Hwin Hr.
  change (windows (ss_mem c1r_ss3)) with [(Some 9%nat, 0, 0); (Some 9%nat, 80, 88)] in Hwin.
  cbn [In] in Hwin.
  destruct Hwin as [Hw | [Hw | []]]; injection Hw as <- <- <-; cbn [base_val] in Hr; [lia|];
    rewrite E9, unsigned_lit_small in Hr by lia; lia. }
assert (F2 : getr (ms_regs ms) 2 = w64 sp1) by (eapply (c1r_reg_pi _ _ _ _ _ 2%nat _ HS); [vm_compute; reflexivity | exact E2]).
assert (F8 : getr (ms_regs ms) 8 = w64 sp0) by (eapply (c1r_reg_pi _ _ _ _ _ 8%nat _ HS); [vm_compute; reflexivity | exact E8]).
assert (F9 : getr (ms_regs ms) 9 = w64 sp1) by (eapply (c1r_reg_pi _ _ _ _ _ 9%nat _ HS); [vm_compute; reflexivity | exact E9]).
assert (F3 : getr (ms_regs ms) 3 = getr (lc_regs cx) 3) by (eapply (c1r_reg_pi _ _ _ _ _ 3%nat _ HS); [vm_compute; reflexivity | exact E3]).
assert (F4 : getr (ms_regs ms) 4 = getr (lc_regs cx) 4) by (eapply (c1r_reg_pi _ _ _ _ _ 4%nat _ HS); [vm_compute; reflexivity | exact E4]).
assert (F18 : getr (ms_regs ms) 18 = w64 SHADOW_OFF) by (eapply (c1r_reg_pi _ _ _ _ _ 18%nat _ HS); [vm_compute; reflexivity | exact E18]).
assert (F20 : getr (ms_regs ms) 20 = w64 r) by (eapply (c1r_reg_pi _ _ _ _ _ 20%nat _ HS); [vm_compute; reflexivity | exact E20]).
assert (F21 : getr (ms_regs ms) 21 = w64 (FF + 64)) by (eapply (c1r_reg_pi _ _ _ _ _ 21%nat _ HS); [vm_compute; reflexivity | exact E21]).
assert (F22 : getr (ms_regs ms) 22 = w64 SHF) by (eapply (c1r_reg_pi _ _ _ _ _ 22%nat _ HS); [vm_compute; reflexivity | exact E22]).
assert (S50f : lslot cx W3 ms 0x50 0).
{ unfold lslot. eapply (lx_word_of_ss W3 ms _ _ 1%nat); [exact HS | reflexivity | rewrite E9; apply unsigned_lit_small; lia
  | cbn [In]; left; reflexivity | reflexivity | lia]. }
assert (S88f : lslot cx W3 ms 0x88 (lc_p cx + Z.of_nat q2)).
{ unfold lslot, lview. apply (c1r_rd_eq _ mem2); [intros j Hj; apply KF; lia | exact C88]. }
assert (S90f : lslot cx W3 ms 0x90 (lc_n cx - Z.of_nat q2)).
{ unfold lslot, lview. rewrite Hn0. apply (c1r_rd_eq _ mem2); [intros j Hj; apply KF; lia | exact C90]. }
assert (KPF : forall a, c1r_out a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- (KP a Ha). apply KF; [exact (c1r_out_range a Ha)|]. destruct Ha as (_ & N50 & _). exact N50. }
apply (HNEXT cx fp k acc ly3 S3 W3 ms _ HB HJ2 HFR HMO).
exists q2, r, fab, bs, M, 0. split.
- apply c1r_carry; [exact Hshape | | exact F20 | exact F21 | exact KPF | ].
  + split; [exact F2|]. split; [exact F8|]. split; [exact F9|]. split; [exact F3|]. split; [exact F4|].
    split; [exact F18 | exact F22].
  + split; [lia|]. split; [exact S88f | exact S90f].
- split; [|split; [exact S50f | lia]].
  split; [exact HML|]. intros j Hj. unfold lview. rewrite KF; [exact (HMAC j Hj) | lia | lia].
Qed.

Lemma c1r_after : forall regs2 mem2 md2 (q2 : nat) (M : list byte),
  ajournal SEGS B LX_STK sp0 [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k ->
  aregs_preserved (ms_regs ms3) regs2 ->
  (forall a, c1r_out a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) mem2 (FF + 32 + j) = Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  (q2 <= length (lc_pl cx))%nat ->
  rdword (aview SEGS (w_H W3) mem2) (sp1 + 0x88) = Some (lc_p cx + Z.of_nat q2) ->
  rdword (aview SEGS (w_H W3) mem2) (sp1 + 0x90) = Some (lc_n cx - Z.of_nat q2) ->
  SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x4e8)) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
intros regs2 mem2 md2 q2 M HJ2 HP KP HML HMAC Hq2 C88 C90.
destruct (Nat.eq_dec q2 (length (lc_pl cx))) as [Heq | Hne].
- exact (c1r_after0 regs2 mem2 md2 q2 M HJ2 HP KP HML HMAC Heq C88 C90).
- exact (c1r_after1 regs2 mem2 md2 q2 M HJ2 HP KP HML HMAC ltac:(lia) C88 C90).
Qed.

Lemma c1r_walk : SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
pose proof c1r_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & EF & Hfin & Hrin & G14 & G15 & G16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HC1 as (HBODY & _ & _ & _ & HBLK & _ & _ & _ & _ & HCUR & HSLL & _ & _ & G20 & G21).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & _ & _ & _ & HINP).
pose proof HREGS as (L2 & L8 & L9 & L3 & L4 & L18 & L22).
pose proof HSLL as (_ & _ & _ & _ & _ & S68 & _ & _).
pose proof HCUR as (Hqle & S88 & S90).
pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & _ & _ & HROD & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & _).
remember (Eimg (Ereg (ms_regs ms3) [w64 (FF + 32)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (ER : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr (ms_regs ms3) x)
  by (intros n x Hx; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hx).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (ER 2%nat (Z_to_bv 5 2) eq_refl); exact L2).
assert (E3 : ew E 3 = getr (lc_regs cx) 3) by (rewrite (ER 3%nat (Z_to_bv 5 3) eq_refl); exact L3).
assert (E4 : ew E 4 = getr (lc_regs cx) 4) by (rewrite (ER 4%nat (Z_to_bv 5 4) eq_refl); exact L4).
assert (E9 : ew E 9 = w64 sp1) by (rewrite (ER 9%nat (Z_to_bv 5 9) eq_refl); exact L9).
assert (E23 : ew E 23 = w64 op) by (rewrite (ER 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (E32 : ew E 32 = w64 (FF + 32)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [w64 (FF + 32)]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear ER.
assert (HS : st_ok_pi SEGS VAL E c1r_ss1 (restrict (w_H W3) ms3)).
{ rewrite (c1r_shape C1_P1 W3 ms3 Hpc Hresv Hsvc Hrom Hfreg Hfcsr).
  unfold c1r_ss1. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, c1r_r68. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 0x68 8 (SOff 32 0) (FF + 32)); [exact (c1r_den E 32 _ E32) | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S68).
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
  - split; [|split; exact I].
    cbn [c1r_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E23, !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r. unfold C1R_SPLO.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS c1r_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose proof HJ as HJa.
paj_run_tok RUN HS HJa SHOK c1r_span.
{ unfold c1r_ss1, c1r_r68. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
  pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end.
clear HF HFr HG.

pose proof (aregs_preserved_of_st_ok SEGS (w_H W3) E _ ms (ms_regs ms3) [w64 (FF + 32)] HS HAE ltac:(vm_compute; reflexivity)) as HP1.
pmkst HS. rewrite pa_sigma_read_mac.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2.
lazymatch type of HS with st_ok _ _ ?ss _ =>
  pose proof (st_ok_restrict_reg SEGS (w_H W3) _ ss ms (11%bv : bv 5) HS) as Ra1;
  let e := eval vm_compute in (sr_get (ss_regs ss) (11%bv : bv 5)) in change (sr_get (ss_regs ss) (11%bv : bv 5)) with e in Ra1 end.
rewrite (c1r_den_and4 E op E23 Hop) in Ra1.

rewrite E2 in Rsp. rewrite E3, Hgp in Rgp. rewrite E4, Htp in Rtp. rewrite E9, unsigned_lit_small in Ra0 by lia.
rewrite E32 in Ra2.
assert (Hsp : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; lia).
rewrite HM in HJa |- *.
pose proof HJa as (HARc & _).
assert (HSTKB : READ_MAC_STKB = 4128) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlen : Z.of_nat (length (skipn q (lc_pl cx))) = lc_n cx - Z.of_nat q) by (rewrite length_skipn; unfold lc_n; lia).
assert (Hsp32 : exists t, sp1 = 32 * t) by (exists (sp1 / 32); pose proof (Z.div_mod sp1 32 ltac:(lia)); lia).
destruct Hsp32 as (t & Ht).
assert (HF64 : exists u, FF = 64 * u) by (exists (FF / 64); pose proof (Z.div_mod FF 64 ltac:(lia)); lia).
destruct HF64 as (u & Hu).
pose proof (c1_rdword_range _ _ _ _ S88) as Rp.
(* the premises of read_mac's contract *)
assert (P1 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P2 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia).
assert (P5 : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp, Ht; replace (32 * t) with ((2 * t) * 16) by lia; apply Z_mod_mult).
assert (P6 : sp0 - LX_STK <= spZ (ms_regs ms) - READ_MAC_STKB) by (rewrite Hsp, HSTKB; unfold LX_STK; lia).
assert (P7 : spZ (ms_regs ms) <= sp0) by lia.
assert (P11 : 0 <= Z.land op 4 < 2 ^ 64) by (pose proof (Z_land_upper op 4 ltac:(lia)); lia).
assert (P12 : (sp1 + 0x88) mod 8 = 0) by (rewrite Ht; replace (32 * t + 0x88) with ((4 * t + 17) * 8) by lia; apply Z_mod_mult).
assert (P13 : spZ (ms_regs ms) <= sp1 + 0x88) by lia.
assert (P14 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (sp1 + 0x88) 8 (lc_p cx + Z.of_nat q))
  by exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S88).
assert (P15 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (sp1 + 0x88 + 8) 8 (Z.of_nat (length (skipn q (lc_pl cx))))).
{ rewrite Hlen. replace (sp1 + 0x88 + 8) with (sp1 + 0x90) by lia. exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S90). }
assert (WIN : forall a, sp1 + 0x88 <= a < sp1 + 0x88 + 16 ->
  awr_byte LX_STK sp0 [] (ablocks B (lc_ly cx) (lc_S cx)) (ablocks B ly3 S3) ly3 [(LX_CID, fp)] a /\
  apresent (w_H W3) (ms_mem ms3) a /\ ~ aowned B ly3 S3 a /\ ly_stk_lo ly3 <= a < ly_stk_hi ly3)
  by (intros a Ha; apply (c1r_stack_win _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJa); unfold LX_STK; lia).
assert (P16 : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (sp1 + 0x88) 16).
{ destruct (WIN (sp1 + 0x88) ltac:(lia)) as (_ & _ & _ & Wl & _).
  destruct (WIN (sp1 + 0x88 + 15) ltac:(lia)) as (_ & _ & _ & _ & Wh).
  exact (c1r_stk_ra ly3 S3 W3 (ms_mem ms3) _ (sp1 + 0x88) 16 HARc Wl ltac:(lia)). }
assert (P17 : tbwr_ok B LX_STK sp0 [] (lc_ly cx) (lc_S cx) ly3 S3 [(LX_CID, fp)] W3 (ms_mem ms3) (spZ (ms_regs ms)) (sp1 + 0x88) 16).
{ intros a Ha. destruct (WIN a Ha) as (Wa & Wp & Wo & _). split; [exact Wa|]. split; [exact Wp|]. split; [exact Wo|].
  rewrite Hsp. lia. }
assert (P19 : skipn q (lc_pl cx) <> [] -> In (lc_p cx, lc_n cx) (ablocks B ly3 S3) /\ lc_p cx <= lc_p cx + Z.of_nat q /\
  lc_p cx + Z.of_nat q + Z.of_nat (length (skipn q (lc_pl cx))) <= lc_p cx + lc_n cx).
{ intros Hne. assert (Hn : 0 < lc_n cx).
  { destruct (Z_lt_le_dec 0 (lc_n cx)) as [Hn|Hn]; [exact Hn|]. exfalso. apply Hne.
    apply length_zero_iff_nil. rewrite length_skipn. unfold lc_n in Hn. lia. }
  pose proof (c1r_inblk Hn) as (Hin & _). split; [exact Hin|]. rewrite Hlen. lia. }
assert (P20 : forall j, 0 <= j < Z.of_nat (length (skipn q (lc_pl cx))) ->
  aview SEGS (w_H W3) (ms_mem ms3) (lc_p cx + Z.of_nat q + j) =
  Some (bv_unsigned (nth (Z.to_nat j) (skipn q (lc_pl cx)) (Z_to_bv 8 0)))).
{ intros j Hj. rewrite Hlen in Hj. rewrite nth_skipn.
  replace (lc_p cx + Z.of_nat q + j) with (lc_p cx + Z.of_nat (q + Z.to_nat j)) by lia.
  replace (q + Z.to_nat j)%nat with (Z.to_nat (Z.of_nat (q + Z.to_nat j))) at 2 by lia.
  apply (c1r_garr8_view W3 (ms_mem ms3) (lc_p cx) (lc_pl cx) _ HINP). unfold lc_n in Hj. lia. }

assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
assert (HF8 : FF / 8 = 8 * u) by (rewrite Hu; replace (64 * u) with ((8 * u) * 8) by lia; apply Z.div_mul; lia).
assert (P21 : afobj SEGS B ly3 S3 W3 (ms_mem ms3) (FF + 32) 6).
{ split.
  - exists LX_CID, fp. split; [exact Hfin|]. split; [unfold LX_CID; lia|]. rewrite EF.
    split; [rewrite Hu; replace (64 * u) with ((8 * u) * 8) by lia; apply Z_mod_mult|].
    rewrite Hfb. lia.
  - split; [rewrite Hu; replace (64 * u + 32) with ((8 * u + 4) * 8) by lia; apply Z_mod_mult|].
    intros x Hx. exists 6.
    assert (Hx8 : x / 8 = 8 * u + 4) by (symmetry; apply (Z.div_unique x 8 (8 * u + 4) (x - 64 * u - 32)); lia).
    split.
    + unfold shadow_of_addr. pose proof (HSH 4%nat ltac:(change (length LSH_iter) with 52%nat; lia)) as Hs4.
      change (nth 4 LSH_iter 0) with 6 in Hs4. unfold lview in Hs4.
      replace (SHADOW_OFF + x / 8) with (SHF + Z.of_nat 4) by (rewrite G10, Hx8, HF8; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      exact Hs4.
    + right. split; [|lia].
      assert (Hm : x mod 8 = x - 64 * u - 32) by (symmetry; apply (Z.mod_unique x 8 (8 * u + 4)); lia). lia. }
assert (P22 : tbwr_ok B LX_STK sp0 [] (lc_ly cx) (lc_S cx) ly3 S3 [(LX_CID, fp)] W3 (ms_mem ms3) (spZ (ms_regs ms)) (FF + 32) 6).
{ intros a Ha.
  assert (Hw : awr_byte LX_STK sp0 [] (ablocks B (lc_ly cx) (lc_S cx)) (ablocks B ly3 S3) ly3 [(LX_CID, fp)] a).
  { right; right; right. exists LX_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EF, Hfb. lia. }
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJa Hw) as [Hp Hno].
  split; [exact Hw|]. split; [exact Hp|]. split; [exact Hno|]. rewrite Hsp, Hes. lia. }
assert (P23 : FF + 32 + 6 <= sp1 + 0x88 \/ sp1 + 0x88 + 16 <= FF + 32) by lia.
assert (P24 : FF + 32 + 6 <= spZ (ms_regs ms) - READ_MAC_STKB \/ spZ (ms_regs ms) <= FF + 32) by (left; rewrite Hsp, HSTKB; lia).
assert (HRO3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms3)))
  by (eapply lx_arodata_kept; [exact HJa | exact HROD]).
destruct (c1r_mbase ly3 S3 W3 (ms_mem ms3) _ HARc HRO3) as (P25 & P26 & P27).
eapply SRr_bind.
{ exact (lh_read_mac B MT HY LX_STK sp0 [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) _ k (ms_regs ms) (sp1 + 0x88) (Z.land op 4) (FF + 32)
    (lc_p cx + Z.of_nat q) (lc_p cx) (lc_n cx) (skipn q (lc_pl cx)) HJa P1 P2 Rgp Rtp P5 P6 P7 Ra0 Ra1 Ra2 P11 P12 P13
    P14 P15 P16 P17 Rp P19 P20 P21 P22 P23 P24 P25 P26 P27). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HMAC & HC0 & HC8 & HKC).

rewrite Rra. rewrite Hsp in HKC. rewrite Hlen in HC0, HC8.
set (U := tbread_mac_used (Z.land op 4) (lc_n cx - Z.of_nat q)) in *.
assert (HU : 0 <= U <= lc_n cx - Z.of_nat q) by (apply c1r_used; unfold lc_n; lia).
pose proof (c1_rdword_range _ _ _ _ S90) as Rn.
assert (Hpn' : lc_p cx + lc_n cx < 2 ^ 64 \/ lc_n cx - Z.of_nat q = 0).
{ destruct (Z_lt_le_dec 0 (lc_n cx)) as [Hn|Hn]; [left; pose proof (c1r_inblk Hn) as (_ & _ & Hpc' & _); lia | right; unfold lc_n in *; lia]. }
apply (c1r_after regs2 mem2 md2 (q + Z.to_nat U) (tbread_mac_out (Z.land op 4) (skipn q (lc_pl cx)))).
- exact HJ2.
- exact (aregs_preserved_trans _ _ _ HP1 HP2).
- exact (c1r_call_keep (ms_mem ms3) mem2 HKC).
- apply lxc1_mac_len.
- exact HMAC.
- unfold lc_n in HU. lia.
- apply rdword_of_val_mem; [|lia].
  replace (lc_p cx + Z.of_nat (q + Z.to_nat U)) with (lc_p cx + Z.of_nat q + U) by lia. exact HC0.
- apply rdword_of_val_mem; [|lia].
  replace (lc_n cx - Z.of_nat (q + Z.to_nat U)) with (lc_n cx - Z.of_nat q - U) by lia.
  replace (sp1 + 0x90) with (sp1 + 136 + 8) by lia. exact HC8.
Qed.

End d.

Theorem c1_seg_read : C1_SEG_read B MT.
Proof.
intros HY POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (q & r & fab & op & bs & HC1 & Hop & Hop3 & Hqle & R19 & R23 & R24 & R26 & R27).
exact (c1r_walk HY POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab op bs HB HJ HFR HMO HC1 Hop R19 R23).
Qed.

End c.
End b.
End a.
