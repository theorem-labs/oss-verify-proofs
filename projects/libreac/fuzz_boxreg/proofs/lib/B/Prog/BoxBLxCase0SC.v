(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 962 of its 1056 lines of code are new or changed and 837 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase1Want.v, with its module paths and module names changed; 188 of its 254 lines of code are new or changed and 990 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, piece SC: from C0_SC (0x8069c, strncmp of
   the new row's name returned 0, a placed row only) through the checks after it to the cut C0_F (0x808f0):
     0x8069c ld a1, 0x48(s1)      a1 = r->n (the slot 0x48)
     0x806a0 bnez a0              -> abort; a0 = 0 at the cut (the seat pins a0 to the literal 0)
     0x806a4 ld a2, 0x20(s1)      a2 = want (the slot 0x20)
     0x806a8 sraiw a0, a2, 31
     0x806ac or a0, a0, a1
     0x806b0 bne s3, a0           -> abort; refuted: want = b >= 0 (Pau's c0_link_placed), so a0 = n = s3
     0x806b4 .. 0x806c0           the ASan check of the row's base field (shadow of s9 = row + 8); the shadow entry
                                  of the registry block (lx_shent_block) resolves it, so the report is not reached
     0x806c4 lw a0, 0(s9)         a0 = the row's base field = b (decl_row_base)
     0x806c8 beq a0, a2           -> 0x808f0 = C0_F; the fall-through (j to the abort) is not reached: base = want
   No instruction of the piece stores, so the seat is the light one of BoxBLxCase0Kit.v (registers as atoms 0 .. 31,
   a0 pinned to 0 and s2 to the shadow offset atom) over two read-only regions: the slots 0x20 and 0x48, and the
   row's base field at s9.  The bytes of the cut are then the bytes of the seat (frame_of_read_only), and the landing
   is the Kit's c0_land.  want and the base field are the same atom (48 = b), so the engine decides beq itself. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBRangeFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs BoxBLxCase0Kit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd read_name_c range_free_c
  lowest_free_c reac_boxreg_declare_c reac_boxreg_declare_inv LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The seat: a0 = 0 (strncmp's result) and s2 = the shadow offset atom (the shadow base of the token check). *)
Definition C0SC_OV : list (bv 5 * sv) := [((10%bv : bv 5), SLit 0); ((18%bv : bv 5), SOff LA_SB 0)].
(* The slots the piece reads: want (0x20, atom 48 = b) and r->n (0x48, = s3, atom 19); both read-only. *)
Definition C0SC_RS : YP09.region := c0k_reg 0x20 0x50 0 0 [(0x20, SOff 48 0); (0x48, SOff 19 0)].
(* The row's base field at s9 = row + 8 (atom 25), read-only. *)
Definition C0SC_RW : YP09.region := YP09.mkRegion (Some 25%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 48 0))].
(* The shadow offset (the token check's base), s9 in application memory, and 0 <= b <= 40. *)
Definition C0SC_G : facts :=
  mkFacts [(LA_SB, mkAF 0x7fff8000 0x7fff8000 0); (25%nat, mkAF 4096 0x7fffff800000 0); (48%nat, mkAF 0 40 0)] [] [].
(* The registry block's bytes row + 8 .. row + 56, over the atom of s9. *)
Definition C0SC_SH : list shent := [mkSHE 25 0 48].
Definition C0SC_BX : sv := SOff LA_SB 0.
Definition C0SC_BSPAN : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).

Lemma c0sc_le4_nth : forall (w : word) j, 0 <= j < 4 ->
  nth (Z.to_nat j) (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4 w) (Z_to_bv 8 0) = byte_of_word w j.
Proof.
  intros w j Hj. unfold OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4, byte_of_word.
  assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3) as [-> | [-> | [-> | ->]]] by lia;
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Z_to_le_bytes nth];
  rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.

(* The bytes of the new row's base field in the table after the declare are those of b. *)
Lemma c0sc_row_byte : forall bs b k p s j, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> 0 <= j < 4 ->
  nth (Z.to_nat (56 * Boxreg.bx_n bs + 8 + j)) (c0_placed bs b k p s) (Z_to_bv 8 0) = byte_of_word (w64 b) j.
Proof.
  intros bs b k p s j HL Hn Hj.
  assert (E : Boxreg.bsub (c0_placed bs b k p s) (56 * Boxreg.bx_n bs + 8) 4 =
              OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4 (Z_to_bv 64 b)).
  { change (c0_placed bs b k p s) with (reac_boxreg_declare_c.decl_bytes bs b k p s).
    rewrite LLVMFuzzerTestOneInput_case0.c0_row_bsub by lia. apply reac_boxreg_declare_inv.decl_row_base. }
  pose proof (BoxregUpd.nth_bsub (c0_placed bs b k p s) (56 * Boxreg.bx_n bs + 8) 4 (Z.to_nat j) ltac:(lia) ltac:(lia))
    as N.
  rewrite E in N. replace (Z.to_nat j <? Z.to_nat 4)%nat with true in N by (symmetry; apply Nat.ltb_lt; lia).
  replace (Z.to_nat (56 * Boxreg.bx_n bs + 8) + Z.to_nat j)%nat with (Z.to_nat (56 * Boxreg.bx_n bs + 8 + j)) in N
    by lia.
  rewrite <- (c0sc_le4_nth (w64 b) j Hj). unfold w64.
  assert (L4 : (Z.to_nat j < length (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4 (Z_to_bv 64 b)))%nat)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.length_le4; lia).
  rewrite (nth_error_nth' _ (Z_to_bv 8 0) L4) in N.
  symmetry in N. exact (nth_error_nth _ _ _ N).
Qed.

(* 0x806a8 sraiw / 0x806ac or: (want >> 31 as a word) | n = n when 0 <= want < 2 ^ 31. *)
Lemma c0sc_denot_idx : forall E na nn a n, ew E na = w64 a -> ew E nn = w64 n -> 0 <= a < 2 ^ 31 ->
  0 <= n < 2 ^ 64 -> sv_denot E (SAlu ALU_OR (SAluw ALU_SRA (SOff na 0) (SLit 31)) (SOff nn 0)) = w64 n.
Proof.
  intros E na nn a n Ha Hn Ha31 Hn64. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu, (U_of_S E (SAluw _ _ _)), S_SAluw, !U_SOff, U_SLit, Ha, Hn. unfold w64.
  rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  rewrite (zcanon_id a) by (unfold M64; lia). rewrite (zcanon_id n) by (unfold M64; lia).
  change (zcanon 31) with 31. rewrite (Z.mod_small a) by lia. change (31 mod 2 ^ 32) with 31.
  cbn [zalu_raw]. change (Z.land 31 31) with 31.
  rewrite (LLVMFuzzerTestOneInput_case0.c0_swrap_small a) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
  change (bv_wrap 64 (bv_swrap 32 0)) with 0. rewrite Z.lor_0_l. apply zcanon_id. unfold M64. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTO := paj_run_to B LAWS.

Lemma c0sc_mbyte : forall (W3 : world SEGS) (ms : machine_state) a (x : byte),
  lview W3 ms a = Some (bv_unsigned x) -> mbyte SEGS (mrestrict (w_H W3) (ms_mem ms)) a = Some x.
Proof.
  intros W3 ms a x H. unfold lview in H. rewrite aview_rd_of in H. unfold rd_of in H.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms)) a) as [y|]; cbn [option_map] in H; [|discriminate].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* The Kit's light seat (c0k_seat) over any symbolic registers sr. *)
Lemma c0sc_seat : forall E (W3 : world SEGS) (ms3 : machine_state) pc sr rs G,
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  regs_ok E sr (ms_regs ms3) -> YP09.regions_wf rs = true ->
  Forall (YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3))) rs ->
  YP09.pairwise_disjoint E rs -> facts_ok E G ->
  st_ok_pi SEGS VAL E (mkSS pc sr rs None G) (restrict (w_H W3) ms3).
Proof.
  intros E W3 ms3 pc sr rs G Hpc Hresv Hpend Hrom Hfregs Hfcsr Hr Hwf Hok Hd HG.
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. apply pa_entry_st_ok_full; assumption.
Qed.

Theorem c0_sc : forall POST i, lx_from B MT POST (C0_F B MT i) -> lx_from B MT POST (C0_SC B MT i).
Proof.
intros POST i HNF cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (pos & r & fab & op & nm & want & b & p & bs & HCOM & HNM & R26 & S60 & HW & Hw & S20 & HPL & HREG
  & R10 & R19 & R23 & R25).
pose proof HCOM as (HBODY & Hi64 & HPREV & HINV & HFAB & Hpos & Hop & Hop3 & HSLL & S58 & S48 & R20 & R21 & R27).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG
  & HS10 & HS18 & HS80 & HINP).
pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HINV as ((HLEN & HB1 & HB2 & HB3 & _) & _).
pose proof HNM as (Hk & Hacc & HBLK & Haf & Hnm4 & Hname & Hcur).
pose proof HJ as (HAR & _).
set (nch := c0_nchv (lc_pl cx) pos) in *.
set (base := c0_basev (lc_pl cx) pos) in *.
set (s := c0_gs (lc_pl cx) pos op) in *.
(* want is the placed base b (Pau's c0_link_placed), and 0 <= b <= 40. *)
assert (Hwb : want = b) by exact (LLVMFuzzerTestOneInput_case0.c0_link_placed _ _ _ _ _ _ HW HPL).
subst want.
assert (Hb0 : 0 <= b) by (destruct HPL as (_ & _ & [(Hx & -> & _) | (_ & _ & Hx & _)]); lia).
assert (Hn4 : 0 <= Boxreg.bx_n bs <= 4) by (destruct HPL as (_ & Hn5 & _); unfold Boxreg.boxreg_B1 in HB1; lia).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in *.
set (rw := r + 56 * Boxreg.bx_n bs) in *.
assert (GEO : c0_geo cx fp [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)]).
{ apply (c0_geo_of B MT cx fp W3 ms3 ly3 S3 md3 k _ HB LAWS HJ HFR).
  - intros pp nn Hin. rewrite HBLK. apply in_or_app. left. exact Hin.
  - pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk. unfold c0_nk.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exists LX_REG. split; [exact Hrin|]. change (req_size LX_REG) with 288. unfold LX_REG. lia.
    + exists (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos) + 1).
      split; [rewrite HBLK; apply in_or_app; right; right; left; reflexivity|].
      pose proof (req_size_pos (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos) + 1) ltac:(lia)) as [_ Hq]. lia. }
assert (Hrsp : r + 288 <= lsp1 cx).
{ pose proof GEO as (_ & _ & _ & _ & _ & _ & G6 & _). inversion G6 as [|? ? Hq _]. cbn [fst snd] in Hq.
  unfold LX_REG in Hq. lia. }
(* ---- the seat ---- *)
set (ex := [w64 b]).
remember (lx_env cx fp (ms_regs ms3) ex) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply lx_env_img).
assert (ER : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr (ms_regs ms3) rr)
  by (intros nn rr Hnn; rewrite HE; apply lx_env_reg; exact Hnn).
assert (E48 : ew E 48 = w64 b) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia))).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (rewrite HE; exact (lx_env_x cx fp (ms_regs ms3) ex 0 ltac:(lia))).
assert (E9 : ew E 9 = w64 (lsp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
assert (E19 : ew E 19 = w64 (Boxreg.bx_n bs)) by (rewrite (ER 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew E 25 = w64 (rw + 8)) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
assert (UB9 : bv_unsigned (ew E 9) = lsp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (UB25 : bv_unsigned (ew E 25) = rw + 8) by (rewrite E25; unfold w64; apply unsigned_lit_small; unfold rw; lia).
assert (HRS : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0SC_RS).
{ unfold YP09.region_ok, C0SC_RS, c0k_reg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply (lx_slot_chunks_ok cx W3 ms3 E). unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite Z.mod_small in S20 by lia.
    apply (lx_slot_atom cx W3 ms3 E 0x20 48 b 0); [rewrite Z.add_0_r; exact S20 | exact E48 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x48 19 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E19 | lia | lia]. }
assert (HRW : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0SC_RW).
{ unfold YP09.region_ok, C0SC_RW.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB25. split; [unfold rw; lia|]. split; [unfold rw; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  intros j Hj. cbn [YP09.c_len YP09.c_val YP09.cv_len YP09.c_off] in Hj |- *. change (Z.of_N 4) with 4 in Hj.
  exists (byte_of_word (w64 b) j). split.
  - cbn [YP09.cbyte]. rewrite lx_sv_SOff0, E48. reflexivity.
  - apply c0sc_mbyte. replace (rw + 8 + 0 + j) with (r + (56 * Boxreg.bx_n bs + 8 + j)) by (unfold rw; lia).
    rewrite (HREG (56 * Boxreg.bx_n bs + 8 + j) ltac:(unfold LX_REG; lia)).
    rewrite c0sc_row_byte by lia. reflexivity. }
assert (HG : facts_ok E C0SC_G).
{ split; [|split; exact I]. cbn [C0SC_G f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  change LA_SB with 32%nat. rewrite E32, E25, E48. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF, rw; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF, rw. repeat split; lia. }
assert (HSR : regs_ok E (lx_sr C0SC_OV) (ms_regs ms3)).
{ apply lx_regs_ok; [rewrite HE; apply lx_regs_ok_atoms|]. unfold C0SC_OV.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite R10. reflexivity.
  - rewrite lx_sv_SOff0. change LA_SB with 32%nat. rewrite E32, G18. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E (mkSS C0P_SC (lx_sr C0SC_OV) [C0SC_RS; C0SC_RW] None C0SC_G) (restrict (w_H W3) ms3)).
{ apply c0sc_seat; try assumption.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; assumption.
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, C0SC_RS, C0SC_RW, c0k_reg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite UB9, UB25. unfold rw. lia. }
assert (U32 : U E (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (U25 : U E (SOff 25 0) = rw + 8) by (apply U_atom; [exact E25 | unfold rw; lia]).
assert (SHOK : sh_ok SEGS C0SC_BX C0SC_SH E (mrestrict (w_H W3) (ms_mem ms3))).
{ unfold sh_ok, C0SC_SH, C0SC_BX. apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E (rw + 8) r LX_REG 0 48 25%nat HAR Hrin U32 U25);
    [unfold rw; lia | lia | change (req_size LX_REG) with 288; unfold rw; lia]. }
(* ---- 0x8069c .. 0x806b0: the bnez of a0 = 0 is decided; stop at bne s3, (want >> 31) | n ---- *)
paj_run_to_tok RUNTO HS HJ SHOK C0SC_BSPAN C0P_F.
{ cbn [ss_mem]. repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]. }
pose proof (frame_of_read_only E [C0SC_RS; C0SC_RW] (ms_mem ms3) (ms_mem ms) eq_refl HF) as HM1.
clear HF HFr HG0.
psrr_branch_tok RUN BR HS SHOK C0SC_BSPAN.
{ (* the abort (idx <> n): refuted, s3 = n = (b >> 31) | n *)
  rewrite (c0k_br_ne E (SOff 19 0) _ (Boxreg.bx_n bs) (Boxreg.bx_n bs) (c0k_atom0 E 19 _ E19 ltac:(lia))
    (c0sc_denot_idx E 48 19 b (Boxreg.bx_n bs) E48 E19 ltac:(lia) ltac:(lia))) in Hc by lia.
  rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* ---- 0x806b4 .. 0x806c8: the shadow check of row + 8 (token), lw = b, beq b, want: to 0x808f0 ---- *)
paj_run_to_tok RUNTO HS HJ SHOK C0SC_BSPAN C0P_F.
{ cbn [ss_mem add_cond]. repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]. }
apply frame_of_read_only in HF; [| vm_compute; reflexivity].
rename HF into HM2. clear HFr HG0.
repeat rewrite wvb_collapse in HJ.
(* ---- the landing at C0_F: no byte changed, the registers of c0_com are the seat's ---- *)
rewrite HM1 in HM2.
assert (K : c0_kept cx fp W3 [] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] (ms_mem ms3) (ms_mem ms0))
  by (intros a _; rewrite HM2; reflexivity).
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
apply (HNF cx fp k acc ly3 S3 W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + C0P_F)) (ms_mem ms0) (seg_rom SEGS)) _
  HB HJ HFR HMO).
assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
destruct (c0_land B MT i cx fp k acc ly3 S3 W3 ms3 (ms_mem ms0) (ms_regs ms0) C0P_SC C0P_F pos r fab op nm bs []
  [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HB HCOM HNM (Forall_nil _) (or_intror (or_introl eq_refl)) K)
  as [HC HN].
- rewrite Q2, (ER 2%nat 2%bv eq_refl). exact G2.
- rewrite Q8, (ER 8%nat 8%bv eq_refl). exact G8.
- rewrite Q9, (ER 9%nat 9%bv eq_refl). exact G9.
- rewrite Q3, (ER 3%nat 3%bv eq_refl). exact G3.
- rewrite Q4, (ER 4%nat 4%bv eq_refl). exact G4.
- rewrite Q18, E32. reflexivity.
- rewrite Q22, (ER 22%nat 22%bv eq_refl). exact G22.
- rewrite Q20, (ER 20%nat 20%bv eq_refl). exact R20.
- rewrite Q21, (ER 21%nat 21%bv eq_refl). exact R21.
- rewrite Q27, (ER 27%nat 27%bv eq_refl). exact R27.
- exists pos, r, fab, op, nm, bs, (c0_placed bs b nch p s).
  split; [exact HC|]. split; [exact HN|].
  split; [exact (c0_slot_keep cx fp W3 [] _ ms3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + C0P_F)) (ms_mem ms0) (seg_rom SEGS))
    K Hsp 0x60 nm ltac:(lia) ltac:(lia) (Forall_nil _) S60)|].
  split; [exact (c0_reg_keep cx fp W3 [] _ ms3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + C0P_F)) (ms_mem ms0) (seg_rom SEGS))
    K r _ (or_introl eq_refl) HREG)|].
  split; [exact (reac_boxreg_declare_inv.reac_boxreg_declare_keeps_inv_holds bs s nch base b p HINV HPL)|].
  split.
  + change (c0_placed bs b nch p s) with (reac_boxreg_declare_c.decl_bytes bs b nch p s).
    rewrite LLVMFuzzerTestOneInput_case0.c0_decl_fabric by lia. exact HFAB.
  + exact (LLVMFuzzerTestOneInput_case0.c0_kept_placed bs b nch p s HINV ltac:(lia)).
Qed.

End a.
