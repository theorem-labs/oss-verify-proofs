(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment GS of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's drain, closed: pb_dr_gs : lib/B/W_drain_cx.v's dr_gs_stmt (DGS 0x83aa4 -> DLN 0x839d4 at S q),
   by lib/B/W_drain_gs.v's dr_gs_of from its three stages, each Qed in its own file:
     pb_gs_scan (lib/B/W_gsscan.v) : gs_scan_stmt   DGS 0x83aa4 -> GA 0x83ba0 / GF 0x83cb4 / DLN 0x839d4
     pb_gs_add  (lib/B/W_gsadd.v)  : gs_add_stmt    GA 0x83ba0 -> DLN 0x839d4
     pb_gs_free (lib/B/W_gsfree.v) : gs_free_stmt   GF 0x83cb4 -> DLN 0x839d4
   Proves no function (kind: segment lemma of drain's image-B walk, GS stage).  The Section header is
   lib/B/W_drain_gs.v's (= lib/B/W_drain_cx.v's), verbatim. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_gs W_gsscan W_gsadd W_gsfree.
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

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

(* ---- The GS stage of drain's image-B walk: the search, then whichever of the two updates it chose.  Each
   stage takes only the Section hypotheses its proof uses; pb_dr_gs takes their union. ---- *)
Theorem pb_dr_gs : dr_gs_stmt B MT MMAX RG.
Proof using LAWS HG HGR HROMO HGO MTL TL ASTRNCMP ASTRLEN AREALLOC AFREE ASTRNDUP ALLOC_TAIL HRGD HGSB HMMAX
  HV9 HSD HSM HCTX_re2 HCTX_fr2 HCTX_sd.
apply dr_gs_of;
  [exact (pb_gs_scan B MT MMAX RG LAWS HG ASTRNCMP ASTRLEN ALLOC_TAIL HGSB HV9 HSD HSM)
  | exact (pb_gs_add B MT MMAX RG LAWS HG HGR HROMO HGO MTL HRGD HGSB HMMAX HV9 HSD HSM CTX_R CTX_S AREALLOC ASTRNDUP
      HCTX_re2 HCTX_sd)
  | exact (pb_gs_free B MT MMAX RG LAWS HG HGR HROMO HGO MTL TL HGSB CTX_F AFREE HCTX_fr2)].
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (image B's DR_x slice D, 2026-10-30): pb_dr_gs_x proves lib/B/W_drain_cx_x.v's
   dr_gs_stmt_x (DGS_x 0x83aa4 -> DLN_x 0x839d4 at S q) over that file's Section variables (B PST ARx MT RP MMAX RG),
   by lib/B/W_drain_gs.v's dr_gs_of_x from the three stage twins, each Qed in its own file:
     pb_gs_scan_x (lib/B/W_gsscan.v) : gs_scan_stmt_x   DGS_x -> GA_x / GF_x / DLN_x
     pb_gs_add_x  (lib/B/W_gsadd.v)  : gs_add_stmt_x    GA_x -> DLN_x
     pb_gs_free_x (lib/B/W_gsfree.v) : gs_free_stmt_x   GF_x -> DLN_x
   the B form of lib/A's dr_gs_of_x (gs_scan_of_loop_x (gs_scan_loop_x ..)) (gs_adda_x (gs_addb_x ..)) (gs_free_x ..)
   (a working branch).  The Section takes the union of the three stages' Section items, in
   lib/B/W_drain_cx_x.v's order and text, and a Theorem Labs lane's shared texts HP0 / BLKN / PSTR, which that file's Section c
   does not have.  Everything above this line is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_cx_x.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
(* lib/B/W_drain_cx_x.v:154 *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* lib/B/W_drain_cx_x.v:156-216, the ones the three stages take *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
(* a Theorem Labs lane's shared texts, the three the stages use (HP0: scan, add, free; BLKN, PSTR: add) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
(* lib/B/W_drain_cx_x.v:219-226: the three allocator rules the stages call and their call-site facts *)
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.


(* ==== route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the R twins of this section's journal-carrying blocks.  Each X_xR
   is X_x with the carriers and engine texts replaced by their R twins (R after the carrier's section
   variables), ajournal_gx_x -> ajournal_gx_xR .. R, ajournal_x -> ajournal_xR .. R and SRr SEGS -> SRrG SEGS R;
   the strict text is untouched.  Blocks that name no journal, no step relation and no carrier have no twin. ==== *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the cf rules at R and the facts their call sites owe, stated once per Section wR (a Theorem Labs lane 21:48Z, option (c));
   they are what the add / free stages take, so they stand here too. *)
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Hypothesis ASTRNDUP_R : astrndup_cf_rule_c_xR SEGS B PST ARx MT MMAX RP CTX_S R (SIGMA WS_strndup).
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_F R.

(* R twin of pb_dr_gs_x: the three stages at R.  Scan is this lane's pb_gs_scan_xR (W_gsscan.v); add and free are
   CfInstMiss-style twins from a Theorem Labs lane's W_gsadd.v / W_gsfree.v (a working branch 2e85f97d9c85). *)
Theorem pb_dr_gs_xR : dr_gs_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
apply dr_gs_of_xR;
  [ exact (pb_gs_scan_xR B PST ARx MT RP MMAX RG LAWS HP0 HG ASTRNCMP ASTRLEN HGSB HV9 HSD HSM R R_trans WLE_R)
  | apply pb_gs_add_xR with (hl := hl) (CTX_R := CTX_R) (CTX_S := CTX_S) (R := R) (RO := RO) (HA := HA); assumption
  | apply pb_gs_free_xR with (hl := hl) (CTX_F := CTX_F) (R := R) (RO := RO); assumption ].
Qed.

End wR.

(* ---- The GS stage of drain's walk over ARx: the search, then whichever of the two updates it chose.  Since part 3c it
   is pb_dr_gs_xR at R := wle (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0), with the strict instance RO := True, HA := True and the strict
   allocator rules lifted to wle (W_journal_x.v arealloc_cf_rule_c_xR_of_x / afree_cf_rule_c_xR_of_x; the strndup rule
   is its R twin at wle by conversion, astrndup_cf_rule_c_x_wle). ---- *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Theorem pb_dr_gs_x : dr_gs_stmt_x B PST ARx MT RP MMAX RG.
Proof.
apply pb_dr_gs_xR with (R := @wle SEGS) (RO := fun _ => True) (HA := fun _ _ _ _ _ _ => True);
  first [ wle_inst | (intros; exact I)
        | (apply arealloc_cf_rule_c_xR_of_x; exact AREALLOC)
        | (apply afree_cf_rule_c_xR_of_x; exact AFREE)
        | exact ASTRNDUP ].
Qed.

End cx.
End bx.
End ax.
