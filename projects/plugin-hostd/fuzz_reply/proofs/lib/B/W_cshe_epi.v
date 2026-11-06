(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the shared base of the image-B (fuzz_reply.asan-ubsan) walk of check_shape_ends: its
   cut points, its frame's saved slots, and the epilogue 0x8592c -> ret, after lib/A/W_check_shape_ends.v (a working branch
   2c323c71eb6) cshe_saved / cshe_epi_m / cshe_epi, a NEW walk over lib/B/W_listing.v (B's body is not A's: B's frame is
   112 bytes where A's is 144, B saves ra and s0..s10 where A also saves s11, and B CALLS list_drop where A inlines free and
   __asan_memmove; VERDICT.md (sha256 810ca1df9ca9; internal record)). *)
(* check_shape_ends at 0x85770 (B; 0x853b0 in A), 0x2ec bytes.  The cut points the pieces of this walk meet at:
     entry      0x85770 (+0x0)      prologue: addi sp,sp,-112; ra at 104, s0..s10 at 96..16
     loop 1     0x85814 (+0xa4)     the counting loop (has_prefix per record), back-edge bnez s8 at 0x85880
     test       0x8588c (+0x11c)    lbu g_gone; beqz -> 0x85964 (the want path), else the gone path
     loop 2     0x858ac (+0x13c)    the gone loop (has_prefix, list_drop at 0x85924), back-edge bgtz s3 at 0x85928
     loop 3     0x8597c (+0x20c)    the want loop (next_line, bcmp, list_find, has_prefix, list_drop at 0x85a00)
     epilogue   0x8592c (+0x1bc)    restores ra, s0..s10 and returns at 0x85960
   The frame bound: the deepest callee B calls is list_drop (LDROP_STK, which covers its free and __asan_memmove); the
   others (has_prefix, next_line, list_find, bcmp) are bounded by less.  W3Checks-2 states B's cshe_spec in the kit
   (lib/B/W_contract.v Section w3, generated); its CSHE_STK reduces to CSHE_STK_B below, and the composition proves that
   equation once. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
(* route R: SRrG and its laws (the R twins of Section c's nested Section wR) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* The sink-instance guard, after every import (MERGE.md (sha256 0694aca87ccd; internal record) item 3) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* the function and its cut points, as offsets of the listing (AF_fr_check_shape_ends = 0x342c, 0x85770) *)
Definition A_csheB : Z := AF_fr_check_shape_ends.
Definition A_csheBP : Z := BASE + A_csheB.
Definition A_csheB_l1 : Z := AF_fr_check_shape_ends + 0xa4.    (* 0x85814, the counting loop *)
Definition A_csheB_tst : Z := AF_fr_check_shape_ends + 0x11c.  (* 0x8588c, the g_gone test (loop 1's join) *)
Definition A_csheB_l2 : Z := AF_fr_check_shape_ends + 0x13c.   (* 0x858ac, the gone loop *)
Definition A_csheB_l3 : Z := AF_fr_check_shape_ends + 0x20c.   (* 0x8597c, the want loop *)
Definition A_csheB_ret : Z := AF_fr_check_shape_ends + 0x1bc.  (* 0x8592c, the epilogue *)

(* the frame (0x85770 addi sp,sp,-112) and the bound: the frame plus list_drop's, the deepest callee *)
Definition CSHE_FRAME_B : Z := 112.
Definition CSHE_STK_B : Z := CSHE_FRAME_B + LDROP_STK.

(* The twelve cells the prologue wrote: ra at sp0 - 8, then s0 .. s10 down to sp0 - 96.  B never writes s11 (x27). *)
Definition cshe_saved_B (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (rs : bvmap 5 word) : Prop :=
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 8) 8 (bv_unsigned (getr rs 1)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 16) 8 (bv_unsigned (getr rs 8)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 24) 8 (bv_unsigned (getr rs 9)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 32) 8 (bv_unsigned (getr rs 18)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 40) 8 (bv_unsigned (getr rs 19)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 48) 8 (bv_unsigned (getr rs 20)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 56) 8 (bv_unsigned (getr rs 21)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 64) 8 (bv_unsigned (getr rs 22)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 72) 8 (bv_unsigned (getr rs 23)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 80) 8 (bv_unsigned (getr rs 24)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 88) 8 (bv_unsigned (getr rs 25)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 96) 8 (bv_unsigned (getr rs 26)).
(* atoms 32 ra, 33 the shadow base (Bx), 34 .. 44 the saved s0, s1, s2 .. s10 *)
Definition cshe_svextra_B (rs : bvmap 5 word) : list word :=
[getr rs 1; Z_to_bv 64 SB; getr rs 8; getr rs 9; getr rs 18; getr rs 19; getr rs 20; getr rs 21;
 getr rs 22; getr rs 23; getr rs 24; getr rs 25; getr rs 26].
Definition cshe_frmR_B : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0
[YP09.mkChunk 16 (CVal 8 (SOff 44 0)); YP09.mkChunk 24 (CVal 8 (SOff 43 0));
 YP09.mkChunk 32 (CVal 8 (SOff 42 0)); YP09.mkChunk 40 (CVal 8 (SOff 41 0));
 YP09.mkChunk 48 (CVal 8 (SOff 40 0)); YP09.mkChunk 56 (CVal 8 (SOff 39 0));
 YP09.mkChunk 64 (CVal 8 (SOff 38 0)); YP09.mkChunk 72 (CVal 8 (SOff 37 0));
 YP09.mkChunk 80 (CVal 8 (SOff 36 0)); YP09.mkChunk 88 (CVal 8 (SOff 35 0));
 YP09.mkChunk 96 (CVal 8 (SOff 34 0)); YP09.mkChunk 104 (CVal 8 (SOff 32 0))].
Definition BxE : sv := SOff 33 0.
Definition BspanE : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cshe_efacts_B : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_cshe_ret_B : sstate := mkSS A_csheB_ret sr_atoms [ cshe_frmR_B ] None cshe_efacts_B.
(* a saved register's value is a 64-bit number, the chunk_ok side goal *)
Ltac cshe_v64 w :=
let H := fresh "Hbr" in pose proof (bv_unsigned_in_range 64 w) as H;
change (bv_modulus 64) with (2 ^ 64) in H; zside.

Section c.
Variable B : asyms.
(* ARx conversion (route (b)): the generic allocator relation ARx with its laws (YCbqG.AR_laws_x) and the placement
   PST, in place of cgif's AR and AR_laws; the interfaces below are stated over the generic journal at the empty ghost
   list (HP0, W_check_shape_ends.v) *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable G : list (Z * Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HG : gx_ok SEGS B G.
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* ---- the walk at the empty ghost list (HP0: every ARx state's ghost list is []): AR0 / AJ0 / AJi0 / AFP0 are cgif's
   AR / journal / inner journal / afn_pre at Hp = [], and each kit lemma the AR walk cites is its _x twin at [] ---- *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x SEGS B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFP0 STK ly S W regs mem md ch := (afn_pre_x SEGS B ARx STK ly S [] W regs mem md ch).

(* The epilogue, in the form a caller that must carry a memory predicate over it needs: the run writes NO byte
   (cshe_frmR_B's writable window is empty), so it hands out the mrestrict equality, from which both the ASan view
   and writability of every byte follow.  cshe_epi_B, below, is this with the view and presence. *)
Lemma cshe_epi_m_B : forall W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
AJ0 G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 112) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> getr regs 27 = getr regs0 27 ->
cshe_saved_B W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall x : word, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  AJ0 G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS W (cfg_at SEGS (BASE + A_csheB_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 H27 HFR HQ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in Hceil. pose proof alloc_ceiling_val as ACV.
destruct HFR as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26).
assert (Hspv : spZ regs = spZ regs0 - 112).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. unfold spZ in Hceil, H47. lia. }
remember (Eimg (Ereg regs (cshe_svextra_B regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E27 : ew E 27 = getr regs 27) by exact (EEo 27%nat 27%bv eq_refl).
assert (E32 : ew E 32 = getr regs0 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs0 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs0 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs0 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs0 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs0 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs0 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs0 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = getr regs0 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = getr regs0 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 112) by (rewrite E2; exact Hspv).
assert (N1 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 104) 8 (bv_unsigned (getr regs0 1)))
  by (replace (spZ regs0 - 112 + 104) with (spZ regs0 - 8) by lia; exact M1).
assert (N8 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 96) 8 (bv_unsigned (getr regs0 8)))
  by (replace (spZ regs0 - 112 + 96) with (spZ regs0 - 16) by lia; exact M8).
assert (N9 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 88) 8 (bv_unsigned (getr regs0 9)))
  by (replace (spZ regs0 - 112 + 88) with (spZ regs0 - 24) by lia; exact M9).
assert (N18 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 80) 8 (bv_unsigned (getr regs0 18)))
  by (replace (spZ regs0 - 112 + 80) with (spZ regs0 - 32) by lia; exact M18).
assert (N19 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 72) 8 (bv_unsigned (getr regs0 19)))
  by (replace (spZ regs0 - 112 + 72) with (spZ regs0 - 40) by lia; exact M19).
assert (N20 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 64) 8 (bv_unsigned (getr regs0 20)))
  by (replace (spZ regs0 - 112 + 64) with (spZ regs0 - 48) by lia; exact M20).
assert (N21 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 56) 8 (bv_unsigned (getr regs0 21)))
  by (replace (spZ regs0 - 112 + 56) with (spZ regs0 - 56) by lia; exact M21).
assert (N22 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 48) 8 (bv_unsigned (getr regs0 22)))
  by (replace (spZ regs0 - 112 + 48) with (spZ regs0 - 64) by lia; exact M22).
assert (N23 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 40) 8 (bv_unsigned (getr regs0 23)))
  by (replace (spZ regs0 - 112 + 40) with (spZ regs0 - 72) by lia; exact M23).
assert (N24 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 32) 8 (bv_unsigned (getr regs0 24)))
  by (replace (spZ regs0 - 112 + 32) with (spZ regs0 - 80) by lia; exact M24).
assert (N25 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 24) 8 (bv_unsigned (getr regs0 25)))
  by (replace (spZ regs0 - 112 + 24) with (spZ regs0 - 88) by lia; exact M25).
assert (N26 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 16) 8 (bv_unsigned (getr regs0 26)))
  by (replace (spZ regs0 - 112 + 16) with (spZ regs0 - 96) by lia; exact M26).
assert (HS : st_ok_pi SEGS VAL E ss_cshe_ret_B
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_csheB_ret)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cshe_ret_B. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, cshe_frmR_B.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
    cbn [base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons); try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 16 8 (SOff 44 0) (bv_unsigned (getr regs0 26)));
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 26) | zside | exact N26].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 24 8 (SOff 43 0) (bv_unsigned (getr regs0 25)));
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 25) | zside | exact N25].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 32 8 (SOff 42 0) (bv_unsigned (getr regs0 24)));
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 24) | zside | exact N24].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 40 8 (SOff 41 0) (bv_unsigned (getr regs0 23)));
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 23) | zside | exact N23].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 48 8 (SOff 40 0) (bv_unsigned (getr regs0 22)));
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 22) | zside | exact N22].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 56 8 (SOff 39 0) (bv_unsigned (getr regs0 21)));
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 21) | zside | exact N21].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 64 8 (SOff 38 0) (bv_unsigned (getr regs0 20)));
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 20) | zside | exact N20].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 72 8 (SOff 37 0) (bv_unsigned (getr regs0 19)));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 19) | zside | exact N19].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 80 8 (SOff 36 0) (bv_unsigned (getr regs0 18)));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 18) | zside | exact N18].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 88 8 (SOff 35 0) (bv_unsigned (getr regs0 9)));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 9) | zside | exact N9].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 96 8 (SOff 34 0) (bv_unsigned (getr regs0 8)));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 8) | zside | exact N8].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 104 8 (SOff 32 0) (bv_unsigned (getr regs0 1)));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 1) | zside | exact N1].
  - apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [cshe_efacts_B f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hceil H47 Hal16 C1 C3 WS ACV. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|].
    apply Z.divide_sub_r; [exact Hal16 | exists 7; reflexivity]. }
assert (SHOK : sh_ok SEGS BxE [] E (mrestrict (w_H W) mem)) by constructor.
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO OUT).
unfold cfg_at. change (w64 (BASE + A_csheB_ret)) with (Z_to_bv 64 (BASE + A_csheB_ret)).
paj_run_tok_x RUNx HS HJ SHOK BspanE.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold cshe_frmR_B. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (HR1 : getr (ms_regs ms) 1 = getr regs0 1) by (rewrite R1; exact E32).
assert (ZB : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r)
  by (intros z r <-; apply Z_to_bv_bv_unsigned).
assert (HPRES : aregs_preserved regs0 (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite (ZB 2 (2%bv : bv 5) eq_refl), R2, Usp.
    replace (spZ regs0 - 112 + 112) with (spZ regs0) by lia.
    unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (ZB 3 (3%bv : bv 5) eq_refl), R3, E3. exact H3.
  - rewrite (ZB 4 (4%bv : bv 5) eq_refl), R4, E4. exact H4.
  - rewrite (ZB 8 (8%bv : bv 5) eq_refl), R8. exact E34.
  - rewrite (ZB 9 (9%bv : bv 5) eq_refl), R9. exact E35.
  - assert (Hr18 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr18 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + rewrite (ZB 18 (18%bv : bv 5) eq_refl), R18. exact E36.
    + rewrite (ZB 19 (19%bv : bv 5) eq_refl), R19. exact E37.
    + rewrite (ZB 20 (20%bv : bv 5) eq_refl), R20. exact E38.
    + rewrite (ZB 21 (21%bv : bv 5) eq_refl), R21. exact E39.
    + rewrite (ZB 22 (22%bv : bv 5) eq_refl), R22. exact E40.
    + rewrite (ZB 23 (23%bv : bv 5) eq_refl), R23. exact E41.
    + rewrite (ZB 24 (24%bv : bv 5) eq_refl), R24. exact E42.
    + rewrite (ZB 25 (25%bv : bv 5) eq_refl), R25. exact E43.
    + rewrite (ZB 26 (26%bv : bv 5) eq_refl), R26. exact E44.
    + rewrite (ZB 27 (27%bv : bv 5) eq_refl), R27, E27. exact H27. }
assert (HKEEP : forall x : word, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (HFr x) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cshe_ret_B In] in Hin. unfold cshe_frmR_B in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
cbn [ms_regs ms_mem]. rewrite HR1, Hra.
apply (HQ (ms_regs ms) (ms_mem ms) _ HPRES HKEEP).
apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
(* Two memories that agree at a byte keep its view, its writability and its presence. *)
Lemma cshe_byte_meq_B : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) -> abyte_kept W1 m W1 m' a.
Proof.
intros W1 m m' a Hq. split.
- unfold aview, mbyte. rewrite Hq. reflexivity.
- unfold writable_at, wview, arm. rewrite Hq. exact (fun H => H).
Qed.
Lemma cshe_apres_meq_B : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) ->
apresent (w_H W1) m a -> apresent (w_H W1) m' a.
Proof.
intros W1 m m' a Hq (Hh & b & Hb). unfold mrestrict in Hq. rewrite Hh in Hq.
split; [exact Hh|]. exists b. rewrite Hq. exact Hb.
Qed.
(* the same, with the ASan view and presence: what loop 2, loop 3 and the composition take *)
Lemma cshe_epi_B : forall W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
AJ0 G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 112) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> getr regs 27 = getr regs0 27 ->
cshe_saved_B W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  AJ0 G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS W (cfg_at SEGS (BASE + A_csheB_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 H27 HFR HQ.
apply (cshe_epi_m_B W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 H27 HFR).
intros regs' mem' md' HPRES HMEQ HJ'. apply (HQ regs' mem' md' HPRES); [| |exact HJ'].
- intros a Ha. apply (aview_eq_of SEGS). apply HMEQ.
- intros a Hp. exact (cshe_apres_meq_B W mem mem' a (HMEQ _) Hp).
Qed.

(* ------------------------------------------------------------------ the pieces' interfaces *)
(* The walk is three pieces and the composition:
     the head    (lib/B/W_cshe_hd.v): entry -> loop 1 -> the g_gone test, ending in cshe_out_B (gone <> 0 and an empty
                 list: 0x858a0 bltz -> the epilogue), cshe_l2_in (gone <> 0, n >= 1) or cshe_l3_in (gone = 0);
     loop 2      (lib/B/W_cshe_l2.v): cshe_l2_in -> cshe_out_B;
     loop 3      (lib/B/W_cshe_l3.v): cshe_l3_in -> cshe_out_B (want = 0 included: 0x8597c blez s6 -> the epilogue);
     composition (lib/B/W_check_shape_ends.v): cshe_out_B -> cshe_epi_B -> the kit's cshe_post.
   Each piece takes, besides these, only premises that are cshe_spec_x's own (lib/B/W_contract_x.v's text, CSHE_STK
   read as CSHE_STK_B) and Section hypotheses from this list, by these names, over the Section variables
   B PST ARx MT RP G {hl} (the generic allocator relation ARx, the placement PST, the room record RP):
     LAWS : AR_laws_x SEGS B ARx hl        ML : ameter_laws MT                 HG : gx_ok SEGS B G
     HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = []
     IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
            fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly)
     BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n
     FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
            ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\
            fs_frame_bytes cid mod 64 = 0
     HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST
     TL : PALib B
     ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp)      NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line)
     LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find)
     LDROP : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
             (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
              ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
             ldrop_spec_x B PST ARx MT RP G' (BASE + AF_fr_list_drop)
             (at the CALLER's G, ldrop_post_x's journal keeps no byte of G, and cshe_spec_x puts HA+64..HA+96 in G,
             so asrc_at could not cross a drop (BCsheL2); this is the Section form of B's pb_list_drop,
             a working branch 436074f627e lib/B/W_list_drop.v:561-572; the walk uses
             G' := [(HA + 80, 16)] and lifts the journal with ajournal_gx_G_mono_x)
     HP : hp_spec_x B PST ARx (BASE + AF_fr_has_prefix)
     HGR : gx_ok SEGS B cshe_ro_B          HGRR : gx_rt B cshe_ro_B
     ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
             (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a)
     HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a
     HEND5S : ashp_x ARx (VAL A_lit_end5) 4 (lib/B/W_contract_x.v ashp_x; lib/B/W_cshe_l3.v takes it unfolded)
     HGS : forall a, VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
           ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
           ~ (VAL A_g_out <= a < VAL A_g_out + 8)
   (B's g_s is A_OBJ 19 = 0x5d8e60; A's is A_OBJ 22.)  cshe_spec_x's prefix home `ashp_x ARx PF (PLEN + 1)` is taken as
   the kit states it. *)
Definition cshe_ro_B : list (Z * Z) :=
[(VAL A_g_gone, 1); (VAL A_g_nout, 8); (VAL A_g_out, 8); (VAL (A_OBJ 19), 384)].  (* A_OBJ 19 = g_s, 0x5d8e60 *)
Section io.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): cshe_spec_x's room record, and the caller's room budget past the call *)
Variable RP : roomp.
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (XO AT HA PF A0 gone : Z) (h : hsrc) (P ob : list byte).
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
(* The epilogue's entry 0x8592c, with everything the kit's cshe_post needs of the run before it. *)
Definition cshe_out_B : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' kk (H' : hlist) (ds : list (Z * list byte)) (c : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_csheB_ret)) mem' (seg_rom SEGS)) md' /\
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly' S' W' mem' md' kk /\
getr regs' 2 = w64 (sp0 - 112) /\ getr regs' 3 = getr regs0 3 /\ getr regs' 4 = getr regs0 4 /\
getr regs' 27 = getr regs0 27 /\
cshe_saved_B W' mem' sp0 regs0 /\
asrc_at B ly' S' W' mem' HA (CheckRep.set_held h H') /\
hl_v H' = hl_v H0 /\ hl_cap H' = hl_cap H0 /\
NoDup (CheckRep.texts H') /\
((gone <> 0 /\
  hl_recs H' = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs H0) /\
  ds = filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs H0) /\ c = 0) \/
 (gone = 0 /\
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H0)) =
  Some (hl_recs H', ds, c))) /\
0 <= c /\
val_mem SEGS (mrestrict (w_H W') mem') AT 8 (A0 + c) /\
val_mem SEGS (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone /\
(forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) ds ++ rest) ->
  Permutation (ablocks B ly' S') rest) /\
frames S' = frames S /\
mo_le MT S S' (hl_n H0 * mo_free MT) /\
(* errno's view is the entry's (W3's cshe_post at a working branch 7ef745aee81: a Theorem Labs lane's ARM_gone needs it) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
(* the room round: the caller's room budget past the call (cshe_post_x's last conjunct) *)
rp_RM RP S' kr.
(* Loop 2's head 0x858ac at its first entry (from 0x858a0-0x858a8, gone <> 0 and n >= 1): s0 = PF, s1 = HA + 80,
   s2 = the shadow byte address of HA + 80, s3 = n, s5 = SB; the allocator state is still the entry's (only
   has_prefix ran, and it allocates nothing); nothing outside [sp0 - CSHE_STK_B, sp0) changed. *)
Definition cshe_l2_in : world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1,
c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l2)) mem1 (seg_rom SEGS)) md1 /\
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly S W1 mem1 md1 0 /\
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 27 = getr regs0 27 /\
getr regs1 8 = w64 PF /\ getr regs1 9 = w64 (HA + 80) /\ getr regs1 18 = w64 ((HA + 80) / 8 + SB) /\
getr regs1 19 = w64 (hl_n H0) /\ getr regs1 21 = w64 SB /\
cshe_saved_B W1 mem1 sp0 regs0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CSHE_STK_B <= a < sp0) -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W1) mem1 a) /\
gone <> 0 /\ 0 < hl_n H0.
(* Loop 3's head 0x8597c at its first entry (from 0x85964-0x85978, gone = 0): s0 = PF, s1 = HA + 80, s2 = AT,
   s3 = " end" (VAL A_lit_end5), s5 = 4, s6 = want, s7 = 5, a0 = want - 1; the rest as cshe_l2_in. *)
Definition cshe_l3_in : world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1,
c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1 /\
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly S W1 mem1 md1 0 /\
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 27 = getr regs0 27 /\
getr regs1 8 = w64 PF /\ getr regs1 9 = w64 (HA + 80) /\ getr regs1 18 = w64 AT /\
getr regs1 19 = w64 (VAL A_lit_end5) /\ getr regs1 21 = w64 4 /\ getr regs1 23 = w64 5 /\
getr regs1 22 = w64 (Z.of_nat (CheckRep.want_of P (hl_recs H0))) /\
getr regs1 10 = w64 (Z.of_nat (CheckRep.want_of P (hl_recs H0)) - 1) /\
cshe_saved_B W1 mem1 sp0 regs0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CSHE_STK_B <= a < sp0) -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W1) mem1 a) /\
gone = 0.
End io.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the epilogue and the pieces' interfaces at a world relation R, for the R twins
   of loop 2 (W_cshe_l2.v cshe_l2_B_xR), loop 3 (W_cshe_l3.v cshe_l3_B_xR) and the composition (W_check_shape_ends.v
   pb_check_shape_ends_xR).  The journal ajournal_gx_x becomes ajournal_gx_xR R (AJ0R, at the empty ghost list as AJ0)
   and SRr SEGS becomes SRrG SEGS R.  cshe_epi_m_B_xR is cshe_epi_m_B's proof with the run over the R journal
   (paj_run_x_xG, W_kit_x.v paj_run_tok_xR) and the strict return step lifted by SRr_SRrG (WLE_R); cshe_out_B_xR /
   cshe_l2_in_xR / cshe_l3_in_xR are the interfaces with the journal at R, and the head's strict facts lift to them
   (cshe_*_xR_of).  The strict texts above keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Local Notation AJ0R G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR SEGS B PST ARx R G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* cshe_epi_m_B at R *)
Lemma cshe_epi_m_B_xR : forall W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
AJ0R G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 112) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> getr regs 27 = getr regs0 27 ->
cshe_saved_B W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall x : word, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  AJ0R G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_csheB_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 H27 HFR HQ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in Hceil. pose proof alloc_ceiling_val as ACV.
destruct HFR as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26).
assert (Hspv : spZ regs = spZ regs0 - 112).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. unfold spZ in Hceil, H47. lia. }
remember (Eimg (Ereg regs (cshe_svextra_B regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E27 : ew E 27 = getr regs 27) by exact (EEo 27%nat 27%bv eq_refl).
assert (E32 : ew E 32 = getr regs0 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs0 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs0 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs0 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs0 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs0 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs0 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs0 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = getr regs0 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = getr regs0 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 112) by (rewrite E2; exact Hspv).
assert (N1 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 104) 8 (bv_unsigned (getr regs0 1)))
  by (replace (spZ regs0 - 112 + 104) with (spZ regs0 - 8) by lia; exact M1).
assert (N8 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 96) 8 (bv_unsigned (getr regs0 8)))
  by (replace (spZ regs0 - 112 + 96) with (spZ regs0 - 16) by lia; exact M8).
assert (N9 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 88) 8 (bv_unsigned (getr regs0 9)))
  by (replace (spZ regs0 - 112 + 88) with (spZ regs0 - 24) by lia; exact M9).
assert (N18 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 80) 8 (bv_unsigned (getr regs0 18)))
  by (replace (spZ regs0 - 112 + 80) with (spZ regs0 - 32) by lia; exact M18).
assert (N19 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 72) 8 (bv_unsigned (getr regs0 19)))
  by (replace (spZ regs0 - 112 + 72) with (spZ regs0 - 40) by lia; exact M19).
assert (N20 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 64) 8 (bv_unsigned (getr regs0 20)))
  by (replace (spZ regs0 - 112 + 64) with (spZ regs0 - 48) by lia; exact M20).
assert (N21 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 56) 8 (bv_unsigned (getr regs0 21)))
  by (replace (spZ regs0 - 112 + 56) with (spZ regs0 - 56) by lia; exact M21).
assert (N22 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 48) 8 (bv_unsigned (getr regs0 22)))
  by (replace (spZ regs0 - 112 + 48) with (spZ regs0 - 64) by lia; exact M22).
assert (N23 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 40) 8 (bv_unsigned (getr regs0 23)))
  by (replace (spZ regs0 - 112 + 40) with (spZ regs0 - 72) by lia; exact M23).
assert (N24 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 32) 8 (bv_unsigned (getr regs0 24)))
  by (replace (spZ regs0 - 112 + 32) with (spZ regs0 - 80) by lia; exact M24).
assert (N25 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 24) 8 (bv_unsigned (getr regs0 25)))
  by (replace (spZ regs0 - 112 + 24) with (spZ regs0 - 88) by lia; exact M25).
assert (N26 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112 + 16) 8 (bv_unsigned (getr regs0 26)))
  by (replace (spZ regs0 - 112 + 16) with (spZ regs0 - 96) by lia; exact M26).
assert (HS : st_ok_pi SEGS VAL E ss_cshe_ret_B
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_csheB_ret)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cshe_ret_B. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, cshe_frmR_B.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
    cbn [base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons); try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 16 8 (SOff 44 0) (bv_unsigned (getr regs0 26)));
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 26) | zside | exact N26].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 24 8 (SOff 43 0) (bv_unsigned (getr regs0 25)));
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 25) | zside | exact N25].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 32 8 (SOff 42 0) (bv_unsigned (getr regs0 24)));
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 24) | zside | exact N24].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 40 8 (SOff 41 0) (bv_unsigned (getr regs0 23)));
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 23) | zside | exact N23].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 48 8 (SOff 40 0) (bv_unsigned (getr regs0 22)));
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 22) | zside | exact N22].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 56 8 (SOff 39 0) (bv_unsigned (getr regs0 21)));
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 21) | zside | exact N21].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 64 8 (SOff 38 0) (bv_unsigned (getr regs0 20)));
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 20) | zside | exact N20].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 72 8 (SOff 37 0) (bv_unsigned (getr regs0 19)));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 19) | zside | exact N19].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 80 8 (SOff 36 0) (bv_unsigned (getr regs0 18)));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 18) | zside | exact N18].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 88 8 (SOff 35 0) (bv_unsigned (getr regs0 9)));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 9) | zside | exact N9].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 96 8 (SOff 34 0) (bv_unsigned (getr regs0 8)));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 8) | zside | exact N8].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 112) 104 8 (SOff 32 0) (bv_unsigned (getr regs0 1)));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 1) | zside | exact N1].
  - apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [cshe_efacts_B f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hceil H47 Hal16 C1 C3 WS ACV. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|].
    apply Z.divide_sub_r; [exact Hal16 | exists 7; reflexivity]. }
assert (SHOK : sh_ok SEGS BxE [] E (mrestrict (w_H W) mem)) by constructor.
pose (RUNx := paj_run_x_xG B PST ARx LAWS R G HG XO OUT).
unfold cfg_at. change (w64 (BASE + A_csheB_ret)) with (Z_to_bv 64 (BASE + A_csheB_ret)).
paj_run_tok_xR RUNx HS HJ SHOK BspanE.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold cshe_frmR_B. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
(* the return moves no world: the strict return step lifts to R *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (HR1 : getr (ms_regs ms) 1 = getr regs0 1) by (rewrite R1; exact E32).
assert (ZB : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r)
  by (intros z r <-; apply Z_to_bv_bv_unsigned).
assert (HPRES : aregs_preserved regs0 (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite (ZB 2 (2%bv : bv 5) eq_refl), R2, Usp.
    replace (spZ regs0 - 112 + 112) with (spZ regs0) by lia.
    unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (ZB 3 (3%bv : bv 5) eq_refl), R3, E3. exact H3.
  - rewrite (ZB 4 (4%bv : bv 5) eq_refl), R4, E4. exact H4.
  - rewrite (ZB 8 (8%bv : bv 5) eq_refl), R8. exact E34.
  - rewrite (ZB 9 (9%bv : bv 5) eq_refl), R9. exact E35.
  - assert (Hr18 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr18 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + rewrite (ZB 18 (18%bv : bv 5) eq_refl), R18. exact E36.
    + rewrite (ZB 19 (19%bv : bv 5) eq_refl), R19. exact E37.
    + rewrite (ZB 20 (20%bv : bv 5) eq_refl), R20. exact E38.
    + rewrite (ZB 21 (21%bv : bv 5) eq_refl), R21. exact E39.
    + rewrite (ZB 22 (22%bv : bv 5) eq_refl), R22. exact E40.
    + rewrite (ZB 23 (23%bv : bv 5) eq_refl), R23. exact E41.
    + rewrite (ZB 24 (24%bv : bv 5) eq_refl), R24. exact E42.
    + rewrite (ZB 25 (25%bv : bv 5) eq_refl), R25. exact E43.
    + rewrite (ZB 26 (26%bv : bv 5) eq_refl), R26. exact E44.
    + rewrite (ZB 27 (27%bv : bv 5) eq_refl), R27, E27. exact H27. }
assert (HKEEP : forall x : word, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (HFr x) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cshe_ret_B In] in Hin. unfold cshe_frmR_B in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
cbn [ms_regs ms_mem]. rewrite HR1, Hra.
apply (HQ (ms_regs ms) (ms_mem ms) _ HPRES HKEEP).
apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
(* cshe_epi_B at R *)
Lemma cshe_epi_B_xR : forall W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
AJ0R G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 112) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> getr regs 27 = getr regs0 27 ->
cshe_saved_B W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  AJ0R G XO OUT CSHE_STK_B (spZ regs0) FP ly0 S0 W0 mem0 md0 [] ly S W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_csheB_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 H27 HFR HQ.
apply (cshe_epi_m_B_xR W0 ly0 S0 mem0 md0 XO OUT FP ly S W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 H27 HFR).
intros regs' mem' md' HPRES HMEQ HJ'. apply (HQ regs' mem' md' HPRES); [| |exact HJ'].
- intros a Ha. apply (aview_eq_of SEGS). apply HMEQ.
- intros a Hp. exact (cshe_apres_meq_B W mem mem' a (HMEQ _) Hp).
Qed.
Section ioR.
Variable MT : ameter_ops.
Variable RP : roomp.
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (XO AT HA PF A0 gone : Z) (h : hsrc) (P ob : list byte).
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
(* cshe_out_B at R *)
Definition cshe_out_B_xR : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' kk (H' : hlist) (ds : list (Z * list byte)) (c : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_csheB_ret)) mem' (seg_rom SEGS)) md' /\
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly' S' W' mem' md' kk /\
getr regs' 2 = w64 (sp0 - 112) /\ getr regs' 3 = getr regs0 3 /\ getr regs' 4 = getr regs0 4 /\
getr regs' 27 = getr regs0 27 /\
cshe_saved_B W' mem' sp0 regs0 /\
asrc_at B ly' S' W' mem' HA (CheckRep.set_held h H') /\
hl_v H' = hl_v H0 /\ hl_cap H' = hl_cap H0 /\
NoDup (CheckRep.texts H') /\
((gone <> 0 /\
  hl_recs H' = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs H0) /\
  ds = filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs H0) /\ c = 0) \/
 (gone = 0 /\
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H0)) =
  Some (hl_recs H', ds, c))) /\
0 <= c /\
val_mem SEGS (mrestrict (w_H W') mem') AT 8 (A0 + c) /\
val_mem SEGS (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone /\
(forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) ds ++ rest) ->
  Permutation (ablocks B ly' S') rest) /\
frames S' = frames S /\
mo_le MT S S' (hl_n H0 * mo_free MT) /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
rp_RM RP S' kr.
(* cshe_l2_in at R *)
Definition cshe_l2_in_xR : world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1,
c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l2)) mem1 (seg_rom SEGS)) md1 /\
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly S W1 mem1 md1 0 /\
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 27 = getr regs0 27 /\
getr regs1 8 = w64 PF /\ getr regs1 9 = w64 (HA + 80) /\ getr regs1 18 = w64 ((HA + 80) / 8 + SB) /\
getr regs1 19 = w64 (hl_n H0) /\ getr regs1 21 = w64 SB /\
cshe_saved_B W1 mem1 sp0 regs0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CSHE_STK_B <= a < sp0) -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W1) mem1 a) /\
gone <> 0 /\ 0 < hl_n H0.
(* cshe_l3_in at R *)
Definition cshe_l3_in_xR : world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1,
c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1 /\
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly S W1 mem1 md1 0 /\
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 27 = getr regs0 27 /\
getr regs1 8 = w64 PF /\ getr regs1 9 = w64 (HA + 80) /\ getr regs1 18 = w64 AT /\
getr regs1 19 = w64 (VAL A_lit_end5) /\ getr regs1 21 = w64 4 /\ getr regs1 23 = w64 5 /\
getr regs1 22 = w64 (Z.of_nat (CheckRep.want_of P (hl_recs H0))) /\
getr regs1 10 = w64 (Z.of_nat (CheckRep.want_of P (hl_recs H0)) - 1) /\
cshe_saved_B W1 mem1 sp0 regs0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CSHE_STK_B <= a < sp0) -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W1) mem1 a) /\
gone = 0.
(* a strict interface fact is one at R (W_journal_x.v ajournal_gx_xR_mono, WLE_R): the head is a strict walk *)
Lemma cshe_out_B_xR_of : forall W' c', cshe_out_B MT RP regs0 ly S W mem md XO AT HA A0 gone h P ob kr W' c' ->
  cshe_out_B_xR W' c'.
Proof.
intros W' c' (ly' & S' & regs' & mem' & md' & kk & H' & ds & c & Hc & HJ & REST).
exists ly', S', regs', mem', md', kk, H', ds, c. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma cshe_l2_in_xR_of : forall W1 c1, cshe_l2_in regs0 ly S W mem md XO AT HA PF gone h W1 c1 -> cshe_l2_in_xR W1 c1.
Proof.
intros W1 c1 (regs1 & mem1 & md1 & Hc & HJ & REST).
exists regs1, mem1, md1. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma cshe_l3_in_xR_of : forall W1 c1, cshe_l3_in regs0 ly S W mem md XO AT HA PF gone h P W1 c1 -> cshe_l3_in_xR W1 c1.
Proof.
intros W1 c1 (regs1 & mem1 & md1 & Hc & HJ & REST).
exists regs1, mem1, md1. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
End ioR.
End wR.
End c.
End b.
End a.
