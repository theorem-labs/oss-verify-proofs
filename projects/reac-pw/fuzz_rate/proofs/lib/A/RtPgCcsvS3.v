(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address below is measured on its
   unstripped twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, whose loaded bytes are
   the same): SEGMENT S3 of the walk of check_csv (0x838e0), from the cut 0x83c40 to the `ret` 0x83d6c.
   Proves lib/A/RtPgCcsvCut.v CC_S3_stmt (kind: segment lemma).

   THE CODE (76 words 0x83c40 .. 0x83d6c, all 4-byte encodings; s2 = s8 = F, s7 = shadow_addr F, s0 = the entry sp):
     0x83c40 lui/addiw a0 = 0x45e0360e; 0x83c48 sd a0,0(s8)     F[0] := the retired magic
     0x83c4c beqz s2,0x83ce0                                     NOT taken: s2 = F >= 4096 (an atom fact), so the
                                                                 20 stores of the real-stack arm 0x83ce0 .. 0x83d2c
                                                                 are dead
     0x83c50 li a0,-11; 0x83c54 .. 0x83cd0 sb a0,k(s7) for k = 0 .. 31   the 32 shadow granules of the frame := 0xf5
     0x83cd4 ld a0,248(s2); 0x83cd8 sb zero,0(a0)                the flag byte of the class-2 frame := 0 (the release)
     0x83cdc j 0x83d30; 0x83d30 addi sp,s0,-160; the 13 restores 0x83d34 .. 0x83d68 (ra, s0, s1, s2 .. s11 from
     sp0 - 8 .. sp0 - 104); 0x83d68 addi sp,sp,160; 0x83d6c ret.
   The release goes through the kit's aj_flag_store (YCbq.v) with astack_free_law_ok (YG0t.v) and the frame flag
   law, which drops the frame from the journal's own list and leaves the state stack_free_state 2 fpos S1; the
   return through SRr_ret_at. The frame's shadow is addressed through the register s7, an atom, so every store is a
   plain SOff and the plain engine runs the whole segment (no shadow_norm). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YK06.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q YG0s YG0t YF0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSiteA RtPgSteps RtPgCcsvKit RtPgCcsvCut.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments, as lib/A/RtPgSteps.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================= the image ======================================= *)
(* the 76 instruction words 0x83c40 .. 0x83d6c *)
Definition CS3_NW : nat := 76.
Definition cs3_tbl : ctable := build_table rsegs CC_PC3 CS3_NW TEmpty.
Lemma cs3_tbl_ok : table_ok rsegs cs3_tbl.
Proof. apply build_table_ok0. unfold CC_PC3. lia. Qed.

(* ======================================= generic lemmas ======================================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a region of the symbolic state is ok for the machine's memory (RPgX01 rx_st_region) *)
Lemma cs3_st_region : forall E ss ms r, st_ok rsegs E ss ms -> In r (ss_mem ss) -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms r (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _) Hin.
exact (proj1 (Forall_forall _ _) Hok r Hin).
Qed.
(* the byte a chunk holding the literal 0 shows (RPgX01 rx_chunk_zero) *)
Lemma cs3_chunk_zero : forall E m base off n,
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal n (SLit 0))) -> (1 <= n)%N ->
mbyte rsegs m (base + off) = Some (Z_to_bv 8 0).
Proof.
intros E m base off n Hc Hn. destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hm, Hb. rewrite !Z.add_0_r in Hm. rewrite Hm. injection Hb as <-.
first [reflexivity | f_equal; vm_compute; reflexivity].
Qed.
(* the flag byte after `sb zero,0(a0)` (RPgX01 rx_flag0_of) *)
Lemma cs3_flag0_of : forall E ss ms n,
st_ok rsegs E ss ms -> In (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) (ss_mem ss) ->
mbyte rsegs (ms_mem ms) (bv_unsigned (ew E n)) = Some (Z_to_bv 8 0).
Proof.
intros E ss ms n HS Hin. pose proof (cs3_st_region E ss ms _ HS Hin) as (_ & _ & _ & Hc).
cbn [YP09.r_chunks YP09.r_base base_val] in Hc. inversion Hc as [|c l Hc0 _]; subst.
rewrite <- (Z.add_0_r (bv_unsigned (ew E n))). exact (cs3_chunk_zero E _ _ 0 1 Hc0 ltac:(lia)).
Qed.
(* a register the run did not touch, or an extra atom (RPgX01 rx_reg_atom / rx_reg_ext / rx_ew_reg) *)
Lemma cs3_reg_atom : forall E ss ms H regs extra (r r' : bv 5) (n : nat),
st_ok rsegs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff n 0 ->
Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros E ss ms H regs extra r r' n HS -> Hg Hn. rewrite (st_ok_restrict_reg rsegs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat regs extra n r' Hn).
Qed.
Lemma cs3_reg_ext : forall E ss ms H regs extra (r : bv 5) (j : nat),
st_ok rsegs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff (32 + j) 0 ->
getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros E ss ms H regs extra r j HS -> Hg. rewrite (st_ok_restrict_reg rsegs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_extra regs extra j).
Qed.
Lemma cs3_ew_reg : forall regs extra (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
bv_unsigned (ew (Ereg regs extra) n) = bv_unsigned (getr regs r).
Proof. intros regs extra n r Hn. rewrite (ew_Ereg_nat regs extra n r Hn). reflexivity. Qed.
(* an 8-byte chunk whose value is the atom n *)
Lemma cs3_chunk8 : forall E m base o (n : nat) v,
ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem rsegs m (base + o) 8 v ->
YP09.chunk_ok rsegs E m base (YP09.mkChunk o (CVal 8 (SOff n 0))).
Proof.
intros E m base o n v Hn Hv Hm.
apply (chunk_ok_val rsegs E m base o 8 (SOff n 0) v).
- exact (rts_den_atom E n v Hn Hv).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn [Z.of_N]. lia.
- change (N.to_nat 8) with 8%nat. exact Hm.
Qed.
(* aowned reads only the layout, the chunks and the frames, so dropping a frame from the state's own list can only
   add owned bytes *)
Lemma cs3_aowned_drop : forall (B : asyms) ly S1 Sc cid pos a,
st_chunks S1 = st_chunks Sc -> frames S1 = (cid, pos) :: frames Sc ->
aowned B ly S1 a -> aowned B ly Sc a.
Proof.
intros B ly S1 Sc cid pos a Ech Efr H.
unfold aowned, sec_extents, aclient_byte in *. rewrite Ech, Efr in H.
destruct H as [H1 H2]. split; [exact H1|].
intros [Hk | (cp & Hcp & Hr)]; apply H2; [left; exact Hk|].
right. exists cp. split; [apply in_cons; exact Hcp | exact Hr].
Qed.
End g.

(* the 13 saved registers, as the engine's atoms 33 .. 45 name them *)
Definition cs3_saved_bv : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma cs3_saved_eq : forall j, (j < 13)%nat -> nth j cs3_saved_bv 0%bv = Z_to_bv 5 (nth j cc_saved_regs 0).
Proof.
intros j Hj. unfold cs3_saved_bv, cc_saved_regs.
do 13 (destruct j as [|j]; [cbn [nth]; apply bv_eq; vm_compute; reflexivity|]). lia.
Qed.
(* env slot 32 is the flag address, 33 + j the entry value of the j-th saved register *)
Definition cs3_X (fl : Z) (regs : bvmap 5 word) : list word :=
Z_to_bv 64 fl :: map (fun r => getr regs r) cs3_saved_bv.
(* the 13 saves at sp0 - 8 .. sp0 - 104, based at the atom of s0 *)
Definition cs3_sv_chunks : list YP09.chunk :=
map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + Nat.succ j) 0))) (seq 0 13).
(* the segment's symbolic memory: the 8 header bytes at F (s8), the 32 shadow granules at shadow_addr F (s7), the
   flag pointer word at F + 248 (s2), the flag byte, and the 13 saves below the entry sp (s0) *)
Definition cs3_mem : smem :=
[ YP09.mkRegion (Some 24%nat) 0 8 0 8 [];
  YP09.mkRegion (Some 23%nat) 0 32 0 32 [];
  YP09.mkRegion (Some 18%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0 cs3_sv_chunks ].
(* F >= 4096 decides `beqz s2` at 0x83c4c; F is 32-aligned *)
Definition cs3_facts : facts := mkFacts [ (18%nat, mkAF 4096 (2 ^ 47) 5) ] [] [].
Definition ss_cs3 : sstate := mkSS CC_PC3 sr_atoms cs3_mem None cs3_facts.

(* a register index as the kit's texts write it (getr regs 2, ...) (RPgX01 z5 / z5g) *)
Ltac z5 H := repeat match type of H with context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) in H by (apply bv_eq; reflexivity) end.
Ltac z5g := repeat match goal with |- context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) by (apply bv_eq; reflexivity) end.
(* the value of a register after a run, from the symbolic state *)
Ltac cs3_atom HS r r' H :=
lazymatch type of HS with st_ok _ (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
assert (H : getr (ms_regs ms) r = getr rg r')
  by (apply (cs3_reg_atom (Ereg rg ex) ss ms Hh rg ex r r' n HS eq_refl); vm_compute; reflexivity) end end.
Ltac cs3_ext HS r H :=
lazymatch type of HS with st_ok _ (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
let j := eval vm_compute in (n - 32)%nat in
assert (H : getr (ms_regs ms) r = nth j ex (Z_to_bv 64 0))
  by (apply (cs3_reg_ext (Ereg rg ex) ss ms Hh rg ex r j HS eq_refl); vm_compute; reflexivity) end end.
Ltac cs3_mach HS m := lazymatch type of HS with st_ok _ _ _ (restrict _ ?x) => rename x into m end.
(* every model a run leaves keeps the I/O state *)
Ltac cs3_io := first [ apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; cs3_io ].
(* the flag-store run (YCbq.v aj_flag_store), applied with its sixteen journal arguments STK .. pos Q. The kit's
   aj_run_flag (YCbq.v:3076) passes fifteen underscores there, one short; this file carries the full count, as
   RPgX01's rx_run_flag does. *)
Ltac cs3_run_flag HS HJ HL Hsegs HML Hwx HASF HFFL :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_runN segs cs3_tbl FUEL ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs cs3_tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (aj_flag_store segs _ HL Hsegs HML cs3_tbl cs3_tbl_ok Hwx HASF HFFL W FUEL E ss ss' st ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ] end end.

(* ======================================= the segment ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
(* the side stack keeps the meter across a set_fs (the allocation and the release are both set_fs) *)
Hypothesis MTF : ameter_fs_laws MT.
(* the allocator's model laws and the side stack's flag law: the two premises of the release *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP rsegs B.

Theorem ccsv_S3 : CC_S3_stmt B MT.
Proof.
unfold CC_S3_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 HST3.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (astack_free_law_ok rsegs B) as ASF.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HST3 as (HPRE & HFR & _ & _).
destruct HPRE as ((HJc & Hraok & Hra4 & Hgp0 & Htp0 & Hal16 & Hwlo & Hwhi & Hev) & _).
destruct HFR as (HJ1 & Hfr1 & Hnin & Habl & Hch1 & _ & _ & _ & _ & Hmo & Hsio & Hkept &
  HF4096 & HFceil & HFapp & HF32 & HFLw & HSV & _ & _ & _ & Hgp1 & Htp1 & Hs0 & Hs2 & Hs7 & Hs8).
(* ---- the frame, its shadow and its flag ---- *)
assert (Hcid : 0 <= CC_CID <= 10) by (unfold CC_CID; lia).
assert (Hin1 : In (CC_CID, fpos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
destruct (rck_jF B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CC_CID fpos HJ1) as [EFA EFL].
destruct (rck_ffacts B LAWS FFL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CC_CID fpos HJ1 Hin1)
  as (_ & _ & _ & _ & HFpres & HFSpres & HFLp & HFLo & _ & _ & HFL4096 & _ & HFLceil).
rewrite <- EFA in HFpres, HFSpres. rewrite <- EFL in HFLp, HFLo, HFL4096, HFLceil.
change (fs_frame_bytes CC_CID) with 256 in HFpres. change (fs_frame_bytes CC_CID / 8) with 32 in HFSpres.
destruct (rck_fbounds CC_CID (frame_addr lyc CC_CID fpos) ltac:(unfold CC_CID; lia) HF32
  ltac:(change (fs_frame_bytes CC_CID) with 256; exact HFapp)) as (_ & _ & HSH0 & HSHceil & HDFS & _).
change (fs_frame_bytes CC_CID / 8) with 32 in HSHceil, HDFS.
change (fs_frame_bytes CC_CID) with 256 in HSHceil, HDFS.
(* the state at the call, and the frame's bounds there *)
pose proof (proj1 HJc) as HARc. pose proof (proj1 HARc) as Mc.
pose proof (proj1 HJ1) as HAR1. pose proof (proj1 HAR1) as M1.
destruct (frame_facts B lyc S1 (aview rsegs (w_H W1) mem1) CC_CID fpos M1 Hin1) as (_ & Hpos & _).
(* ---- the stack window: the saves lie far above the side stack ---- *)
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & HSTKnn & Hceil0 & Hslo & Hshi & H47 & _).
assert (HSPlo : alloc_ceiling + 8368 <= spZ regs) by (unfold T_csv_STK, ESTACK in *; lia).
assert (HSPhi : spZ regs <= 2 ^ 47) by lia.
assert (HSP64 : 0 <= spZ regs < 2 ^ 64)
  by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as X;
      change (bv_modulus 64) with (2 ^ 64) in X; lia).
(* ---- the three quantities ---- *)
set (SP := spZ regs) in *.
set (F := frame_addr lyc CC_CID fpos) in *.
set (FL := flag_addr lyc CC_CID fpos) in *.
set (shF := shadow_addr F) in *.
(* the flag byte is not in the frame and not in the frame's shadow *)
assert (HFLnF : FL + 1 <= F \/ F + 256 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 256)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres FL ltac:(lia)) HFLo). }
assert (HFLnS : FL + 1 <= shF \/ shF + 32 <= FL).
{ destruct (Z_lt_ge_dec FL shF) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (shF + 32)) as [Hlt2|Hge2]; [exfalso | right; lia].
  replace FL with (shF + (FL - shF)) in HFLo by lia.
  exact (proj2 (HFSpres (FL - shF) ltac:(lia)) HFLo). }
(* the frame, its shadow and its flag are the runtime's at the call: the frame is free there *)
assert (HOF : forall a, F <= a < F + 256 -> aowned B lyc Sc a).
{ intros a Ha. exact (own_free_frame B lyc Sc (aview rsegs (w_H W) memc) CC_CID fpos a Mc Hcid Hpos Hnin Ha). }
assert (HOS : forall a, shF <= a < shF + 32 -> aowned B lyc Sc a).
{ intros a Ha.
  exact (own_free_frame_shadow B lyc Sc (aview rsegs (w_H W) memc) CC_CID fpos a Mc Hcid Hpos Hnin Ha). }
assert (HOFL : aowned B lyc Sc FL) by exact (cs3_aowned_drop B lyc S1 Sc CC_CID fpos FL Hch1 Hfr1 HFLo).
(* ---- the entry state at 0x83c40 ---- *)
unfold cfg_at. change (w64 CC_PC3) with (Z_to_bv 64 CC_PC3).
assert (B24 : bv_unsigned (ew (Ereg regs1 (cs3_X FL regs)) 24) = F).
{ rewrite (cs3_ew_reg regs1 (cs3_X FL regs) 24 (24%bv : bv 5) ltac:(vm_compute; reflexivity)), Hs8.
  apply unsigned_lit_small; lia. }
assert (B23 : bv_unsigned (ew (Ereg regs1 (cs3_X FL regs)) 23) = shF).
{ rewrite (cs3_ew_reg regs1 (cs3_X FL regs) 23 (23%bv : bv 5) ltac:(vm_compute; reflexivity)), Hs7.
  apply unsigned_lit_small; lia. }
assert (B18 : bv_unsigned (ew (Ereg regs1 (cs3_X FL regs)) 18) = F).
{ rewrite (cs3_ew_reg regs1 (cs3_X FL regs) 18 (18%bv : bv 5) ltac:(vm_compute; reflexivity)), Hs2.
  apply unsigned_lit_small; lia. }
assert (B8 : bv_unsigned (ew (Ereg regs1 (cs3_X FL regs)) 8) = SP).
{ rewrite (cs3_ew_reg regs1 (cs3_X FL regs) 8 (8%bv : bv 5) ltac:(vm_compute; reflexivity)), Hs0.
  apply unsigned_lit_small; lia. }
assert (E32 : ew (Ereg regs1 (cs3_X FL regs)) 32 = Z_to_bv 64 FL)
  by exact (ew_Ereg_extra regs1 (cs3_X FL regs) 0).
assert (B32 : bv_unsigned (ew (Ereg regs1 (cs3_X FL regs)) 32) = FL)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs1 (cs3_X FL regs)) ss_cs3
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 CC_PC3) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_cs3. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold cs3_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B24. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (HFpres (F + o) ltac:(lia))).
    + rewrite B23. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (HFSpres o ltac:(lia))).
    + rewrite B18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (cs3_chunk8 _ _ F 248 32 FL E32 ltac:(lia)).
      apply val_mem_of_rdword. exact HFLw.
    + rewrite B32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable rsegs). exact HFLp.
    + rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold cs3_sv_chunks. rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      apply (chunk_ok_val rsegs _ _ SP (-8 - 8 * Z.of_nat j) 8 (SOff (32 + Nat.succ j) 0)
        (bv_unsigned (getr regs (nth j cs3_saved_bv 0%bv)))).
      * cbn [sv_denot]. rewrite Z.add_0_r, (ew_Ereg_extra regs1 (cs3_X FL regs) (Nat.succ j)),
          !Z_to_bv_bv_unsigned.
        destruct Hj as [_ Hj]. unfold cs3_X, cs3_saved_bv.
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      * pose proof (bv_unsigned_in_range 64 (getr regs (nth j cs3_saved_bv 0%bv))) as Y.
        change (bv_modulus 64) with (2 ^ 64) in Y. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn [Z.of_N]. lia.
      * change (N.to_nat 8) with 8%nat.
        rewrite (cs3_saved_eq j ltac:(lia)).
        replace (SP + (-8 - 8 * Z.of_nat j)) with (SP - 8 - 8 * Z.of_nat j) by lia.
        apply val_mem_of_rdword. apply HSV. lia.
  - unfold cs3_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B24, ?B23, ?B18, ?B32, ?B8.
    repeat split; try exact I;
      destruct HDFS as [HD|HD], HFLnF as [HN1|HN1], HFLnS as [HN2|HN2]; lia.
  - unfold cs3_facts. split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B18. change (2 ^ 5) with 32.
    change (2 ^ 47) with 140737488355328.
    split; [lia|]. split; [exact HF32 | lia]. }
(* ---- the run: the retired magic, the 32 granules 0xf5 and the flag store ---- *)
cs3_run_flag HS HJ1 LAWS Hsegs ML Hwx ASF FFL.
- unfold CC_CID. lia.
- intros a (r & Hin & Ha). unfold ss_cs3, cs3_mem in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?B24, ?B23, ?B18, ?B32, ?B8 in Ha.
  + left. apply (rck_awr_fobj STK sp0 FP _ _ lyc
      ((CC_CID, fpos) :: own) CC_CID fpos a ltac:(left; reflexivity)).
    assert (HR : F <= a < F + 256) by lia. exact HR.
  + left. apply (rck_awr_fsh STK sp0 FP _ _ lyc
      ((CC_CID, fpos) :: own) CC_CID fpos a ltac:(left; reflexivity)).
    assert (HR : shF <= a < shF + 32) by lia. exact HR.
  + exfalso. lia.
  + right. change (flag_addr lyc CC_CID fpos) with FL. lia.
  + exfalso. lia.
- intros msr HSr. change (flag_addr lyc CC_CID fpos) with FL. rewrite <- B32.
  apply (cs3_flag0_of _ _ msr 32%nat HSr).
  cbn [ss_mem In]. repeat first [ (left; reflexivity) | right ].
- (* ---- the leaf: the epilogue and the `ret` ---- *)
  cs3_mach HS msD.
  eapply (SRr_ret_at rsegs cs3_tbl cs3_tbl_ok Hwx W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta.
  cs3_ext HS (1%bv : bv 5) R0.
  assert (R1 : getr (ms_regs msD) (1%bv : bv 5) = getr regs 1)
    by (rewrite R0; unfold cs3_X, cs3_saved_bv; reflexivity).
  unfold cc_post, rt_cpost_o, rt_cpost_g. cbv beta.
  eexists. exists lyc, (stack_free_state CC_CID fpos S1), (ms_regs msD), (ms_mem msD). eexists.
  (* the return pc is ra *)
  split.
  { rewrite R1. unfold YK0s.ret_ok in Hraok. rewrite Hraok. reflexivity. }
  (* the float state is untouched *)
  split; [reflexivity|].
  (* the journal *)
  split; [eapply ajournal_materialize; eassumption|].
  (* the 13 restores *)
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr. z5 Hgp1. z5 Htp1. z5 Hs0.
    destruct Hr' as [->|[->|[->|Hr']]].
    - z5g. cs3_atom HS (2%bv : bv 5) (8%bv : bv 5) Hx. rewrite Hx, Hs0.
      change SP with (spZ regs). unfold spZ, w64. apply Z_to_bv_bv_unsigned.
    - z5g. cs3_atom HS (3%bv : bv 5) (3%bv : bv 5) Hx. rewrite Hx. exact Hgp1.
    - z5g. cs3_atom HS (4%bv : bv 5) (4%bv : bv 5) Hx. rewrite Hx. exact Htp1.
    - destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; z5g;
      lazymatch goal with |- getr _ ?rr = _ => cs3_ext HS rr Hx end;
      rewrite Hx; unfold cs3_X, cs3_saved_bv; reflexivity. }
  (* frames *)
  assert (Efr2 : frames (stack_free_state CC_CID fpos S1) = frames Sc).
  { change (del_pos (frames S1) CC_CID fpos = frames Sc). rewrite Hfr1. cbn [del_pos].
    rewrite !Z.eqb_refl. reflexivity. }
  split; [exact Efr2|].
  (* the owned set at the return is the owned set at the call *)
  split; [exact (rck_aowned_of B lyc (stack_free_state CC_CID fpos S1) lyc Sc eq_refl Hch1 Efr2)|].
  (* the blocks *)
  assert (Eab : ablocks B lyc (stack_free_state CC_CID fpos S1) = ablocks B lyc Sc).
  { unfold ablocks. rewrite blocks_stack_free_state. exact Habl. }
  split; [rewrite Eab; apply Permutation_refl|].
  (* the I/O state *)
  split; [eapply same_io_trans; [exact Hsio | cs3_io]|].
  (* the meter *)
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  (* every byte outside the stack window and outside the owned set at the call is as at the call *)
  split; [|exact I].
  intros a Ha Hstkw Hown.
  assert (KE : aview rsegs (w_H W1) (ms_mem msD) a = aview rsegs (w_H W1) mem1 a).
  { apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
    intros (r & Hin & Hw). unfold ss_cs3, cs3_mem in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?B24, ?B23, ?B18, ?B32, ?B8 in Hw.
    - exact (Hown (HOF a ltac:(lia))).
    - exact (Hown (HOS a ltac:(lia))).
    - lia.
    - apply Hown. replace a with FL by lia. exact HOFL.
    - lia. }
  rewrite KE. exact (Hkept a Ha Hstkw Hown).
Qed.
End m.

About ccsv_S3.
Print Assumptions ccsv_S3.
