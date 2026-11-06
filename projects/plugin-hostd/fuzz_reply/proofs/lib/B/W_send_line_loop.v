(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the loop segment of fuzz_reply's send_line walk on IMAGE B
   (fuzz_reply.asan-ubsan), in the form of the cgif donor's loop over concrete cut states
   (proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v tcbb_loopX).  Structure ported from image A's
   lib/A/W_send_line_loop.v (a working branch 9367674296a / ccd62d4c6f6: sl_arm_eintr, sl_arm_dead, sl_arm_data,
   pb_sl_loop_cut) and from the old image-B walk a working branch 37280b674f71 lib/B/Prog/send_line_loop.v
   and send_line_run.v (the rounds from the loop top 0x828f8). *)
(* The loop head L = 0x828f8 (A_sl_loop).  Every round first runs B's UBSan checks of the copy's source line + sent
   (0x828fc PTR_BLTU `bltu s2,s1`, closed by W_traps.v trap_ptr_bltu; 0x82908 NULL_XOR, which the runner folds to
   `beqz (xor s8, 0)` with s8 seated as atom 24 = 1, closed by trap_null_xor_folded), then the
   g_client test (an abort when it is not 3, decided by the state: g_client is 3 at L), then one of
   - the EINTR round: g_send_eintr <> 0, cleared, errno := EINTR, errno read back and found EINTR (0x82980 .. 0x829a0:
     its NONNULL / ALIGN4 / NONNULL_LIT traps 0x82928, 0x82930, 0x82984, 0x82988 decided by the seated errno atom),
     back to L with the bound one smaller;
   - the dead round: g_send_dead <> 0, errno := EPIPE (traps 0x8295c, 0x82964 decided), errno read back and found
     not EINTR, g_client_broken := 1, out through the epilogue;
   - a data round: n = min(len - sent, g_send_max or len - sent) at the cut N = 0x829cc, then either the growth half
     (W_send_line_cx.v sl_grow_stmt: g_out short) or straight to the join J = 0x82a08, and the copy half there
     (sl_copy_stmt).
   The Section header is W_send_line_cx.v's, verbatim. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin W_traps W_send_line_rb
W_send_line_cx W_send_line_md.
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
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_nout RG.
Hypothesis HH18 : VAL (A_HI 18) + 1212 = rg_client_broken RG.
Hypothesis HH20 : VAL (A_HI 20) + 1372 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 1328 = rg_send_dead RG.
Hypothesis HH22 : VAL (A_HI 22) + 1252 = rg_send_max RG.
Hypothesis HH23 : VAL (A_HI 23) + 1372 = rg_nout RG.
Hypothesis HH24 : VAL (A_HI 24) + 1976 = rg_capout RG.
Hypothesis HH25 : VAL (A_HI 25) + 2000 = rg_out RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
Let RUN := paj_run_x B LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Definition LBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---- where the cells lie: image bytes of B's band [0x10000, 0x5fc000) ---- *)
Lemma sl_inG_img : forall a, inG (G_SL B RG) a -> 0x10000 <= a < 0x5fc000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HG a Ha))). Qed.
Lemma sl_inGO_img : forall a, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a -> 0x10000 <= a < 0x5fc000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HGO a Ha))). Qed.
Ltac ing_tac := unfold G_SL; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
Lemma sl_bands :
(0x10000 <= rg_client RG /\ rg_client RG + 4 <= 0x5fc000) /\
(0x10000 <= rg_client_broken RG /\ rg_client_broken RG + 1 <= 0x5fc000) /\
(0x10000 <= rg_send_eintr RG /\ rg_send_eintr RG + 1 <= 0x5fc000) /\
(0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= 0x5fc000) /\
(0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fc000) /\
(0x10000 <= rg_nout RG /\ rg_nout RG + 8 <= 0x5fc000) /\
(0x10000 <= rg_capout RG /\ rg_capout RG + 8 <= 0x5fc000) /\
(0x10000 <= rg_out RG /\ rg_out RG + 8 <= 0x5fc000) /\
(0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fc000).
Proof.
assert (GO : forall x n, In (x, n) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] -> 0 < n ->
  0x10000 <= x /\ x + n <= 0x5fc000).
{ intros x n Hin Hn.
  pose proof (sl_inGO_img x ltac:(unfold inG; apply Exists_exists; exists (x, n); split; [exact Hin | unfold in_zr; cbn; lia])).
  pose proof (sl_inGO_img (x + n - 1) ltac:(unfold inG; apply Exists_exists; exists (x, n); split; [exact Hin | unfold in_zr; cbn; lia])).
  lia. }
assert (GL : forall x n, In (x, n) (G_SL B RG) -> 0 < n -> 0x10000 <= x /\ x + n <= 0x5fc000).
{ intros x n Hin Hn.
  pose proof (sl_inG_img x ltac:(unfold inG; apply Exists_exists; exists (x, n); split; [exact Hin | unfold in_zr; cbn; lia])).
  pose proof (sl_inG_img (x + n - 1) ltac:(unfold inG; apply Exists_exists; exists (x, n); split; [exact Hin | unfold in_zr; cbn; lia])).
  lia. }
Ltac w_in := repeat (first [left; reflexivity | right]).
split; [apply GO; [w_in | lia]|]. split; [apply GL; [unfold G_SL; w_in | lia]|].
split; [apply GL; [unfold G_SL; w_in | lia]|]. split; [apply GO; [w_in | lia]|].
split; [apply GO; [w_in | lia]|]. split; [apply GL; [unfold G_SL; w_in | lia]|].
split; [apply GL; [unfold G_SL; w_in | lia]|]. split; [apply GL; [unfold G_SL; w_in | lia]|].
apply GL; [unfold G_SL; w_in | lia].
Qed.

(* ---- the loop head's symbolic state ---- *)
(* The three kept auipc registers must be the listing's own hi atoms, because a PLdHi slot only runs when its base
   register still holds SOff (A_HI j) 0, and a store through s10 / s6 finds its region by that atom; s11 is pinned to
   EINTR so that the errno compare at 0x829a0 decides; s8, the one-time flag `snez s1` (= 1), stays its own atom with
   the fact [1, 1] (W_traps.v's seat recipe R3), so that the NULL_XOR check of 0x82908, which the runner folds to
   `xor s8, 0` once it knows line + sent <> 0, is trap_null_xor_folded's shape. *)
Definition sr_L : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms
    27%bv (SLit 4))
    21%bv (SOff (A_HI 17) 0))
    26%bv (SOff (A_HI 20) 0))
    22%bv (SOff (A_HI 23) 0).
Definition r_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 40 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff (A_HI 18) 0)); YP09.mkChunk 8 (CVal 8 (SOff (A_HI 22) 0));
   YP09.mkChunk 16 (CVal 8 (SOff (A_HI 24) 0)); YP09.mkChunk 24 (CVal 8 (SOff (A_HI 25) 0));
   YP09.mkChunk 32 (CVal 8 (SOff (A_HI 21) 0))].
Definition r_client : YP09.region := YP09.mkRegion (Some (A_OBJ 9)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 3))].
Definition r_eintr : YP09.region := YP09.mkRegion (Some (A_OBJ 11)) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition r_dead : YP09.region := YP09.mkRegion (Some (A_HI 21)) 1328 1329 1328 1328 [YP09.mkChunk 1328 (CVal 1 (SOff 33 0))].
Definition r_max : YP09.region := YP09.mkRegion (Some (A_HI 22)) 1252 1260 1252 1252 [YP09.mkChunk 1252 (CVal 8 (SOff 37 0))].
Definition r_nout : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition r_capout : YP09.region := YP09.mkRegion (Some (A_HI 24)) 1976 1984 1976 1984 [YP09.mkChunk 1976 (CVal 8 (SOff 35 0))].
Definition r_out : YP09.region := YP09.mkRegion (Some (A_HI 25)) 2000 2008 2000 2008 [YP09.mkChunk 2000 (CVal 8 (SOff 36 0))].
Definition r_broken : YP09.region := YP09.mkRegion (Some (A_HI 18)) 1212 1213 1212 1213 [YP09.mkChunk 1212 (CVal 1 (SLit 0))].
Definition l_regions : smem :=
  [ r_frame; r_client; r_eintr; r_dead; r_max; r_nout; r_capout; r_out; r_broken ].

Definition OBJF : afact := mkAF 0x10000 0x5fc000 0.
Definition HIF : afact := mkAF 0 0x5fc000 0.
Definition l_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (25%nat, mkAF SB SB 0); (24%nat, mkAF 1 1 0);
  (8%nat, mkAF 1 (2^63 - 1) 0); (9%nat, mkAF 4096 (2^63 - 1) 0); (23%nat, mkAF 0 (2^63 - 1) 0);
  (32%nat, mkAF 0 1 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 0 (2^47) 0);
  (35%nat, mkAF 0 (2^47) 0); (36%nat, mkAF 0 (2^47) 0); (37%nat, mkAF 0 255 0);
  (A_OBJ 11, OBJF); (A_OBJ 12, OBJF);
  (A_HI 18, HIF); (A_HI 20, HIF); (A_HI 21, HIF); (A_HI 22, HIF); (A_HI 23, HIF); (A_HI 24, HIF); (A_HI 25, HIF) ] [] [].

Definition ss_L : sstate := mkSS A_sl_loop sr_L l_regions None l_facts.
Definition BxL : sv := SOff 25 0.
Definition l_extra (eiL dd no' capL outL mx : Z) : list word :=
  map (Z_to_bv 64) [eiL; dd; no'; capL; outL; mx].

Lemma sl_loop_entry : forall lyL SL (WL : world SEGS) regsL memL sp0 len line sent eiL dd no' capL outL mx evL O',
spZ regsL = sp0 - SL_FRAME ->
2 ^ 46 + SL_FRAME <= sp0 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
sl_regsL regsL len line sent ->
1 <= len <= 2 ^ 63 - 1 -> 4096 <= line <= 2 ^ 63 - 1 -> 0 <= sent <= 2 ^ 63 - 1 ->
sl_spill WL memL (sp0 - SL_FRAME) ->
aout_at B RG lyL SL WL memL (CTL 3 0 dd eiL evL) O' mx no' capL outL ->
0 <= no' <= 2 ^ 47 -> 0 <= capL <= 2 ^ 47 -> 0 <= outL <= 2 ^ 47 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsL (l_extra eiL dd no' capL outL mx))) ss_L
(restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS))).
Proof.
intros lyL SL WL regsL memL sp0 len line sent eiL dd no' capL outL mx evL O'
Hsp Hlo Hhi Hal HR Hlen Hline Hsent HSP HOUT Rno Rcap Rout.
unfold SL_FRAME in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof sl_bands as (Bcl & Bbr & Bei & Bdd & Bmx & Bno & Bcap & Bout & Berr).
destruct HR as (R8 & R9 & R23 & R24 & R25 & R27 & R21 & R26 & R22).
destruct HSP as (M0 & M8 & M16 & M24 & M32).
destruct HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hcl & Hbr & Hdd & Hei & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev, Hcl, Hbr, Hdd, Hei.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsL (l_extra eiL dd no' capL outL mx))).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regsL 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regsL 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 9 9%bv eq_refl)).
assert (E23 : ew E 23 = getr regsL 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 23 23%bv eq_refl)).
assert (E25 : ew E 25 = getr regsL 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 25 25%bv eq_refl)).
assert (E24 : ew E 24 = getr regsL 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 24 24%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 dd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 no') by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (UV : forall n, (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew E n) = VAL n).
{ intros n Hn. subst E. rewrite Eimg_img by exact Hn. apply unsigned_lit_small. apply pa_val_range. }
assert (BV : forall n, (A_TEXT <= n < A_LIM)%nat -> base_val E (Some n) = VAL n).
{ intros n Hn. cbn [base_val]. exact (UV n Hn). }
assert (SVH : forall n, (A_TEXT <= n < A_LIM)%nat -> sv_denot E (SOff n 0) = w64 (VAL n)).
{ intros n Hn. cbn [sv_denot]. rewrite (UV n Hn). rewrite Z.add_0_r. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; exact Hsp).
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 11 ltac:(lia)) as Q11.
pose proof (pa_obj_img 12 ltac:(lia)) as Q12. pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
unfold ss_L, A_sl_loop. apply pa_entry_st_ok_full.
- unfold sr_L.
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 23)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R22].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 20)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R26].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 17)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R21].
  apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R27].
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold l_regions, r_frame, r_client, r_eintr, r_dead, r_max, r_nout, r_capout, r_out, r_broken.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (sp0 - 144) 0 8 (SOff (A_HI 18) 0) (VAL (A_HI 18)));
      [rewrite (SVH (A_HI 18)) by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity
      | pose proof (pa_val_range (A_HI 18)); zside | zside | rewrite Z.add_0_r; exact M0].
    * apply (chunk_ok_val SEGS E _ (sp0 - 144) 8 8 (SOff (A_HI 22) 0) (VAL (A_HI 22)));
      [rewrite (SVH (A_HI 22)) by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity
      | pose proof (pa_val_range (A_HI 22)); zside | zside | exact M8].
    * apply (chunk_ok_val SEGS E _ (sp0 - 144) 16 8 (SOff (A_HI 24) 0) (VAL (A_HI 24)));
      [rewrite (SVH (A_HI 24)) by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity
      | pose proof (pa_val_range (A_HI 24)); zside | zside | exact M16].
    * apply (chunk_ok_val SEGS E _ (sp0 - 144) 24 8 (SOff (A_HI 25) 0) (VAL (A_HI 25)));
      [rewrite (SVH (A_HI 25)) by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity
      | pose proof (pa_val_range (A_HI 25)); zside | zside | exact M24].
    * apply (chunk_ok_val SEGS E _ (sp0 - 144) 32 8 (SOff (A_HI 21) 0) (VAL (A_HI 21)));
      [rewrite (SVH (A_HI 21)) by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity
      | pose proof (pa_val_range (A_HI 21)); zside | zside | exact M32].
  + rewrite (BV (A_OBJ 9)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_client RG) 0 4 (SLit 3) 3);
    [cbn [sv_denot]; reflexivity | zside | zside |].
    rewrite Z.add_0_r. replace 3 with (3 mod 2 ^ 32) by reflexivity. exact Vcl.
  + rewrite (BV (A_OBJ 11)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV11.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wei; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_send_eintr RG) 0 1 (SOff 32 0) eiL);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vei.
  + rewrite (BV (A_HI 21)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (VAL (A_HI 21)) 1328 1 (SOff 33 0) dd);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite HH21. exact Vdd.
  + rewrite (BV (A_HI 22)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (VAL (A_HI 22)) 1252 8 (SOff 37 0) mx);
    [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite HH22. exact Vmx.
  + rewrite (BV (A_OBJ 12)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV12.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wno; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_nout RG) 0 8 (SOff 34 0) no');
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vno.
  + rewrite (BV (A_HI 24)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. replace (VAL (A_HI 24) + o) with (rg_capout RG + (o - 1976)) by lia. apply Wcap. lia.
    * repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_HI 24)) 1976 8 (SOff 35 0) capL);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite HH24. exact Vcap.
  + rewrite (BV (A_HI 25)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. replace (VAL (A_HI 25) + o) with (rg_out RG + (o - 2000)) by lia. apply Wout. lia.
    * repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_HI 25)) 2000 8 (SOff 36 0) outL);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite HH25. exact Vout.
  + rewrite (BV (A_HI 18)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. replace (VAL (A_HI 18) + o) with (rg_client_broken RG + (o - 1212)) by lia. apply Wbr. lia.
    * repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_HI 18)) 1212 1 (SLit 0) 0);
      [cbn [sv_denot]; reflexivity | zside | zside |].
      rewrite HH18. exact Vbr.
- apply pairwise_disjoint_of_extents.
  unfold l_regions, r_frame, r_client, r_eintr, r_dead, r_max, r_nout, r_capout, r_out, r_broken, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (BV (A_OBJ 9)), (BV (A_OBJ 11)), (BV (A_HI 21)), (BV (A_HI 22)), (BV (A_OBJ 12)),
          (BV (A_HI 24)), (BV (A_HI 25)), (BV (A_HI 18)) by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  cbn [base_val]. rewrite Usp, HV9, HV11, HV12.
  replace (VAL (A_HI 21)) with (rg_send_dead RG - 1328) by lia.
  replace (VAL (A_HI 22)) with (rg_send_max RG - 1252) by lia.
  replace (VAL (A_HI 24)) with (rg_capout RG - 1976) by lia.
  replace (VAL (A_HI 25)) with (rg_out RG - 2000) by lia.
  replace (VAL (A_HI 18)) with (rg_client_broken RG - 1212) by lia.
  cbn [zpairwise_disjoint zall_disjoint] in HRGD. unfold zdisj in HRGD. cbn [fst snd] in HRGD.
  destruct HRGD as (_ & _ &
   (D01 & D02 & D03 & D04 & D05 & D06 & D07 & _ & _) &
   (D08 & D09 & D10 & D11 & D12 & D13 & _ & _) &
   (D14 & D15 & D16 & D17 & D18 & _ & _) &
   (D19 & D20 & D21 & D22 & _ & _) &
   (D23 & D24 & D25 & _ & _) &
   (D26 & D27 & _ & _) &
   (D28 & _ & _) & _ & _ & _).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split;
  first [ solve [ clear - Hlo C1 Bcl Bbr Bei Bdd Bmx Bno Bcap Bout; lia ]
        | match goal with H : _ \/ _ |- _ => solve [ clear - H; lia ] end ].
- split; [|split; [exact I | exact I]].
  cbn [l_facts f_atoms atoms_ok]. unfold afact_ok, OBJF, HIF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E8, E9, E23, E25, E24, E32, E33, E34, E35, E36, E37.
  rewrite R8, R9, R23, R25, R24.
  rewrite (UV (A_OBJ 11)), (UV (A_OBJ 12)),
          (UV (A_HI 18)), (UV (A_HI 20)), (UV (A_HI 21)), (UV (A_HI 22)), (UV (A_HI 23)), (UV (A_HI 24)), (UV (A_HI 25))
    by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I;
  first [ rewrite Zminus_mod, Hal; reflexivity
        | solve [ clear - Hlo Hhi Hlen Hline Hsent Hei Hdd Rno Rcap Rout Hmxr Q11 Q12
                    HH18 HH20 HH21 HH22 HH23 HH24 HH25 HV11 HV12 Bbr Bei Bdd Bmx Bno Bcap Bout; unfold SB; lia ] ].
Qed.

(* The donor's paj_run_tok / paj_run_to_tok with a fuel that fits one round (W_kit's FUEL is 200000). *)
Definition L_FUEL : N := 3000%N.
Ltac lrun RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH L_FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH L_FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "lrun: no img_env" end in
eapply (RUN W L_FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
end.
Ltac lrun_to RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH L_FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH L_FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "lrun_to: no img_env" end in
eapply (RUNTO W L_FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
end.

(* The write windows of a run's regions are G_SL cells (or empty).  NALL holds the placement equations in the
   numeral form vm_compute leaves (A_OBJ 11 = 252, A_OBJ 12 = 253, A_HI 18 = 298, A_HI 20 = 300, A_HI 23 = 303,
   A_HI 24 = 304, A_HI 25 = 305); a region based on an errno atom carries `base_val E (Some n) = as_errno B`. *)
Ltac awr_empty :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; intros a Ha; exfalso; clear - Ha; lia.
Ltac l_awr_g :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
  first
  [ lazymatch goal with BA : base_val ?E (Some ?m) = as_errno B |- forall a, base_val ?E (Some ?m) + _ <= a < _ -> _ =>
      rewrite BA end; intros a Ha; clear - Ha; ing_tac
  | lazymatch goal with BVE : forall _, _ -> base_val ?E _ = _ |- forall a, base_val ?E (Some ?m) + _ <= a < _ -> _ =>
      rewrite (BVE m) by (repeat match goal with X : _ |- _ => clear X end; unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia) end;
    intros a Ha;
    lazymatch goal with NA : VAL 252%nat = rg_send_eintr RG /\ _ |- _ => clear - Ha NA end; ing_tac ].
Ltac l_awr :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first [ apply awr_ok_x_nil | apply awr_ok_x_cons; [awr_empty|] | apply awr_ok_x_cons_g; [l_awr_g|] ].

Ltac sl_intro HI :=
unfold SLI in HI;
destruct HI as (lyL & SL & kL & evL & capL & outL & spent & rest &
  HJ & Hsp & H3 & H4 & Hgp & Htp & HraE & HR & HSP & HSV & Hcl & Hbr & Hsent & Hei1 & Hei2 & Hdd1 & Hev &
  HOUT & HGL & Hline0 & Hline1 & HROM & HLOK & HLG & Hcapq & Hdd2 & HMM & HLM & HAPK & HMOK & HMLE & HCOST & Hspent0 &
  HPerm0 & HPerm1 & HFR).

(* HRGD as the zdisj fact of two of its extents, named by their positions in the list:
   0 VAL (A_OBJ 0), 1 VAL (A_OBJ 30), 2 g_client, 3 g_client_broken, 4 g_send_eintr, 5 g_send_dead,
   6 g_send_max, 7 g_nout, 8 g_capout, 9 g_out, 10 errno *)
Lemma sl_rgd : forall i j, i <> j -> (i < 11)%nat -> (j < 11)%nat ->
zdisj (nth i [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)] (0, 0))
(nth j [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)] (0, 0)).
Proof. intros i j Hij Hi Hj. apply zpairwise_disjoint_nth; [exact HRGD | exact Hij | cbn; lia | cbn; lia]. Qed.
(* errno apart from the eight cells of aout_at the walk keeps in its regions *)
Lemma sl_errno_apart :
(as_errno B + 4 <= rg_client RG \/ rg_client RG + 4 <= as_errno B) /\
(as_errno B + 4 <= rg_client_broken RG \/ rg_client_broken RG + 1 <= as_errno B) /\
(as_errno B + 4 <= rg_send_eintr RG \/ rg_send_eintr RG + 1 <= as_errno B) /\
(as_errno B + 4 <= rg_send_dead RG \/ rg_send_dead RG + 1 <= as_errno B) /\
(as_errno B + 4 <= rg_send_max RG \/ rg_send_max RG + 8 <= as_errno B) /\
(as_errno B + 4 <= rg_nout RG \/ rg_nout RG + 8 <= as_errno B) /\
(as_errno B + 4 <= rg_capout RG \/ rg_capout RG + 8 <= as_errno B) /\
(as_errno B + 4 <= rg_out RG \/ rg_out RG + 8 <= as_errno B).
Proof.
pose proof (sl_rgd 10 2 ltac:(lia) ltac:(lia) ltac:(lia)) as D2. pose proof (sl_rgd 10 3 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
pose proof (sl_rgd 10 4 ltac:(lia) ltac:(lia) ltac:(lia)) as D4. pose proof (sl_rgd 10 5 ltac:(lia) ltac:(lia) ltac:(lia)) as D5.
pose proof (sl_rgd 10 6 ltac:(lia) ltac:(lia) ltac:(lia)) as D6. pose proof (sl_rgd 10 7 ltac:(lia) ltac:(lia) ltac:(lia)) as D7.
pose proof (sl_rgd 10 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D8. pose proof (sl_rgd 10 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D9.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9. unfold zdisj in D2, D3, D4, D5, D6, D7, D8, D9.
cbn [fst snd] in D2, D3, D4, D5, D6, D7, D8, D9. repeat split; lia.
Qed.

(* A value is carried by a frame that keeps the view of its bytes. *)
Lemma vm_keep : forall (W : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v HK Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
apply HK. lia.
Qed.
Lemma garr8_keep : forall (W : world SEGS) m m' a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l HK Hg. apply (garr8_frame SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) m') a l Hg).
intros x Hx. apply (mbyte_of_aview SEGS). exact (HK x Hx).
Qed.
(* Two memories that hold the same value at a cell view its bytes alike. *)
Lemma aview_of_vm2 : forall (W : world SEGS) m m' a n v,
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v ->
forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x.
Proof.
intros W m m' a n v H1 H2 x Hx. unfold aview.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H1 (Z.to_nat (x - a)) ltac:(lia)), (H2 (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.
(* An image atom's word. *)
Lemma ew_img : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = Z_to_bv 64 (VAL n).
Proof.
intros E n HE Hn. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* errno's four bytes are addressable: HERRZ puts them inside one of the instance's zero-shadow ranges. *)
Lemma errno_ra : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (as_errno B) 4.
Proof.
intros ly S W mem md HAR.
destruct HERRZ as (r & Hin & H8 & Hlo & Hhi).
assert (Hin' : In r (zero_shadow_ranges B ly)) by (unfold zero_shadow_ranges; right; exact Hin).
pose proof (al_zshadow _ _ LAWS ly S W mem md r HAR Hin') as HZ.
pose proof HAR as (M & _).
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ M)) r Hin) as (R1 & R2 & R3 & R4 & R5).
pose proof (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF (fst r) (snd r) R3 R4 HZ) as HRA.
pose proof (Z.mul_div_le (snd r) 8 ltac:(lia)) as Hq.
intros y Hy. apply HRA. clear - Hy Hlo Hhi Hq. lia.
Qed.
Ltac clia := repeat match goal with X : _ |- _ => clear X end; lia.
(* the latest run's machine state, frame and growth, renamed (a run that stops at a call leaves st_ok, not st_ok_pi) *)
Ltac rn msN frN grN :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msN
  | HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msN end;
  lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msN)) |- _ => rename H into frN end;
  lazymatch goal with H : mem_grows _ (mrestrict _ (ms_mem msN)) |- _ => rename H into grN end;
  try lazymatch goal with H : frame_of _ _ (ms_mem _) (ms_mem msN) |- _ => clear H end.
(* a byte outside G_SL is outside every write window of a run's regions: each window is empty, a G_SL cell (a region
   based on an image atom, with NALL's placement), or errno (a region based on the errno atom) *)
Ltac nowr_g HnG :=
  let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (rr & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      first [ solve [ clear - Hr; lia ]
            | solve [ exfalso; apply HnG;
                lazymatch type of Hr with context [base_val ?E (Some ?m)] =>
                  first [ lazymatch goal with BA : base_val E (Some m) = as_errno B |- _ => rewrite BA in Hr end
                        | lazymatch goal with BVE : forall _, _ -> base_val E _ = _ |- _ =>
                            rewrite (BVE m) in Hr by (repeat match goal with X : _ |- _ => clear X end; cbv; lia) end ] end;
                lazymatch goal with NA : VAL 252%nat = rg_send_eintr RG /\ _ |- _ => clear - Hr NA end; ing_tac ] ] | ]);
  try destruct Hin.

(* the cells of aout_at as the loop head's regions hold them: read off a state whose regions are l_regions' (with
   g_send_eintr's region on its object atom 252 or rebased on hi 300 + 1372), shifted by k regions in front *)
Lemma sl_aout_blks_in : forall ly S W mem c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W mem c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.

(* ---- The exit: the epilogue, then sl_post from the concrete facts at 0x82aa0. ---- *)
Lemma sl_exit : forall regsE ly S W mem md c O mx no cap out Bl lyX SX WX regsX memX mdX k out' rest,
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S W mem md [] lyX SX WX memX mdX k ->
spZ regsX = spZ regsE - SL_FRAME -> getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (spZ regsE - SL_FRAME) regsE ->
apres_kept B W mem WX memX ->
mo_le MT S SX (sl_cost MT c mx no cap (Z.of_nat (length Bl))) ->
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) ->
Permutation (ablocks B lyX SX) (aout_blks (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ++ rest) ->
aout_at B RG lyX SX WX memX (sl_ctl c (Z.of_nat (length Bl))) (sl_O c O Bl) mx (sl_no c no (Z.of_nat (length Bl)))
  (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ->
(sl_live c (Z.of_nat (length Bl)) = false -> out' = out) ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros regsE ly S W mem md c O mx no cap out Bl lyX SX WX regsX memX mdX k out' rest HJ Hsp H3 H4 Hra HSV HAPK HMLE HP1 HP2 HOUT HOFF.
apply (sl_epi B RG LAWS HG W ly S mem md (spZ regsE) _ lyX SX WX regsX memX mdX k regsE _ HJ eq_refl Hsp H3 H4 Hra HSV).
intros regs' mem' md' HP Hm' HJ'.
assert (GRX : mem_grows (mrestrict (w_H WX) memX) (mrestrict (w_H WX) mem')) by (intros x Hx; rewrite Hm'; exact Hx).
exists lyX, SX, regs', mem', md', k, out'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP|].
split; [intros a H1 H2 H3' Hp; exact (apresent_grows _ _ _ _ GRX (HAPK a H1 H2 H3' Hp))|].
split; [exact HMLE|].
split; [exists rest; split; [exact HP1 | exact HP2]|].
split; [|exact HOFF].
apply (aout_at_kept B RG lyX SX WX memX lyX SX WX mem' _ _ _ _ _ _ HOUT); [|intros b Hb; exact (sl_aout_blks_in _ _ _ _ _ _ _ _ _ _ HOUT b Hb)].
intros r _ a _. split.
- exact (aview_eq_of SEGS (w_H WX) memX mem' a (Hm' _)).
- unfold arm. apply writable_kept. intros Hp. exact (apresent_grows _ _ _ _ GRX Hp).
Qed.

(* Everything SLI / SLM says of a memory carries to a memory with the same view at every byte and no less presence. *)
Lemma aview_all_of_bounded : forall H (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' HV a. rewrite (aview_wrap64 H m' a), (aview_wrap64 H m a). apply HV. apply Z.mod_pos_bound. lia.
Qed.
Lemma sl_moved : forall (W' : world SEGS) m m',
(forall a, aview SEGS (w_H W') m' a = aview SEGS (w_H W') m a) ->
(forall a, apresent (w_H W') m a -> apresent (w_H W') m' a) ->
(forall ly' S' c' O' mx' no' cap' out', aout_at B RG ly' S' W' m c' O' mx' no' cap' out' ->
   aout_at B RG ly' S' W' m' c' O' mx' no' cap' out') /\
(forall line l, garr8 SEGS (arm W' m) line l -> garr8 SEGS (arm W' m') line l) /\
(rom_view SEGS W' m -> rom_view SEGS W' m') /\
(forall a n v, val_mem SEGS (mrestrict (w_H W') m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v).
Proof.
intros W' m m' HV HP.
split; [|split; [|split]].
- intros ly' S' c' O' mx' no' cap' out' HOUT.
  apply (aout_at_kept B RG ly' S' W' m ly' S' W' m' _ _ _ _ _ _ HOUT); [|exact (sl_aout_blks_in _ _ _ _ _ _ _ _ _ _ HOUT)].
  intros r _ a _. split; [exact (HV a)|]. apply writable_kept. exact (HP _).
- intros line l Hg. apply (garr8_frame SEGS (mrestrict (w_H W') m) (mrestrict (w_H W') m') line l Hg).
  intros x _. apply (mbyte_of_aview SEGS). exact (HV x).
- intros HR a Ha. rewrite (HV a). exact (HR a Ha).
- intros a n v Hv. apply (vm_keep W' m m' a n v); [intros x _; exact (HV x) | exact Hv].
Qed.

(* ---- The prelude of every round (written out in each arm: an Ltac definition cannot name the hypotheses its
   callee tactics introduce): SLI's facts, the loop head's state, and the head of the round up to the g_send_eintr
   test at 0x8291c: the two UBSan checks of line + sent (0x828fc PTR_BLTU, trap_ptr_bltu; 0x82908 NULL_XOR, folded by
   the runner to `xor s8, 0`, trap_null_xor_folded) and the g_client test (decided). ---- *)

(* send_line's EINTR round: g_send_eintr <> 0 (then sent = 0): g_send_eintr := 0, errno := EINTR, errno read back
   (EINTR: the round continues), back to L with sent = 0, g_send_eintr = 0 *)
Lemma sl_arm_eintr : forall n, sl_loop_at B MT MMAX RG n -> forall regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL -> eiL <> 0 ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat (Datatypes.S n) ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hne Hb.
(* ---- round prelude (begin) ---- *)
sl_intro HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & HstkL & _).
pose proof HstkL as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresL.
assert (WS : SL_STK = 16528) by reflexivity.
assert (HSF : SL_FRAME = 144) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev, Hclr, Hbrr, Hddr, Heir.
assert (Rcapout : 0 <= capL /\ 0 <= outL /\ no + sent <= 2 ^ 47 /\ capL <= 2 ^ 47 /\ outL <= 2 ^ 47).
{ destruct Hblk as [(Hz0 & Hz1 & Hz2) | (Hz3 & Hz4 & Hin1 & _)]; [repeat split; lia|].
  destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hin1) as (_ & Hp4 & Hpc & _).
  assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
  rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
assert (Hlen1 : 1 <= len <= 2 ^ 63 - 1) by lia.
assert (Hline4 : 4096 <= line).
{ destruct HLOK as [H0 | [(q & m & Hin & _ & Hq & _) | (Himg & _ & _)]]; [lia | |].
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL q m HARL Hin) as (_ & H4096 & _); lia.
  - pose proof (pa_img_range line (Himg line ltac:(lia))); lia. }
pose proof (sl_loop_entry lyL SL WL regsL memL (spZ regsE) len line sent eiL (ct_dd c)
  (no + sent) capL outL mx evL (O ++ firstn (Z.to_nat sent) Bl)
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR Hlen1 ltac:(lia) ltac:(lia)
  HSP HOUT ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
pose proof sl_bands as (Bcl & Bbr & Bei & Bdd & Bmx & Bno & Bcap & Bout & Berr).
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0 WS; lia).
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R23 & R24 & R25 & R27 & R21 & R26 & R22).
remember (Eimg (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsL 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact R9).
assert (E23 : ew E 23 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = w64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = w64 (ct_dd c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = w64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = w64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = w64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (NALL : VAL 252%nat = rg_send_eintr RG /\ VAL 253%nat = rg_nout RG /\ VAL 298%nat + 1212 = rg_client_broken RG /\
  VAL 300%nat + 1372 = rg_send_eintr RG /\ VAL 303%nat + 1372 = rg_nout RG /\ VAL 304%nat + 1976 = rg_capout RG /\
  VAL 305%nat + 2000 = rg_out RG)
  by (repeat split; first [exact HV11 | exact HV12 | exact HH18 | exact HH20 | exact HH23 | exact HH24 | exact HH25]).
assert (N9 : VAL 250%nat = rg_client RG) by exact HV9.
assert (N11 : VAL 252%nat = rg_send_eintr RG) by exact HV11.
assert (N12 : VAL 253%nat = rg_nout RG) by exact HV12.
assert (N18 : VAL 298%nat + 1212 = rg_client_broken RG) by exact HH18.
assert (N20 : VAL 300%nat + 1372 = rg_send_eintr RG) by exact HH20.
assert (N21 : VAL 301%nat + 1328 = rg_send_dead RG) by exact HH21.
assert (N22 : VAL 302%nat + 1252 = rg_send_max RG) by exact HH22.
assert (N23 : VAL 303%nat + 1372 = rg_nout RG) by exact HH23.
assert (N24 : VAL 304%nat + 1976 = rg_capout RG) by exact HH24.
assert (N25 : VAL 305%nat + 2000 = rg_out RG) by exact HH25.
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WL) memL)) by constructor.
assert (U9 : U E (SOff 9 0) = line) by (apply U_atom; [exact E9 | lia]).
assert (U23 : U E (SOff 23 0) = sent) by (apply U_atom; [exact E23 | lia]).
assert (UADD : U E (SAlu ALU_ADD (SOff 9 0) (SOff 23 0)) = line + sent)
  by (apply (trap_U_add E _ _ line sent U9 U23); lia).
(* 0x828f8 add s2,s1,s7; 0x828fc PTR_BLTU bltu s2,s1 -> unimp *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH1 FH1 GH1.
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite (trap_ptr_bltu E (SOff 9 0) (SAlu ALU_ADD (SOff 9 0) (SOff 23 0)) line (line + sent) U9 UADD
    ltac:(lia)) in Hc. discriminate Hc. }
(* 0x82900 seqz; xor s8; 0x82908 NULL_XOR beqz -> unimp *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH2 FH2 GH2.
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite (trap_null_xor_folded E 24 E24) in Hc0. discriminate Hc0. }
(* the g_client test (bne g_client, 3 -> abort: decided, g_client is 3), the load of g_send_eintr, to its beqz *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH3 FH3 GH3.
(* ---- round prelude (end) ---- *)
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc1 by (clear - Heir; lia).
  apply Hne. apply Z.eqb_eq in Hc1. lia. }
(* g_send_eintr <> 0: the EINTR round *)
rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc1 by (clear - Heir; lia).
assert (HeiE : eiL = 1) by (clear - Hc1 Heir; apply Z.eqb_neq in Hc1; lia).
assert (HREL : VAL (A_OBJ 11) = VAL (A_HI 20) + 1372) by (rewrite HV11, <- HH20; reflexivity).
prebase HS 2%nat (A_HI 20) 1372 HREL.
(* sb zero,1372(s10) (g_send_eintr := 0), to the jal __errno_location at 0x82924 *)
lrun RUN HS HJ SHOK LBspan. { l_awr. }
rn msP FP0 GP0.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_SL B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
    (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
    WL (ms_regs msP) (ms_mem msP) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out))
    ly S W mem md ([] : list (Z * Z)) lyL SL _ kL (- SL_FRAME) (Z_to_bv 64 (BASE + 1508)) HG eq_refl HJ).
  - unfold spZ at 1. rewrite Q2, Usp. clear. unfold SL_FRAME. lia.
  - unfold SL_FRAME. reflexivity.
  - unfold SL_FRAME. clear. lia.
  - clear. lia.
  - clear. vm_compute. intros Hx. discriminate Hx.
  - rewrite Q3, E3, H3. exact Hgp.
  - rewrite Q4, E4, H4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros _. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE _. exact (AERRNO lyL SL WL (ms_regs msP) (ms_mem msP) _ HPRE). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
assert (WRc : forall a, writable_at SEGS (arm WL memL) a -> writable_at SEGS (mrestrict (w_H WL) mem2) a).
{ intros a Ha. apply (writable_kept (w_H WL) (ms_mem msP) mem2 a (fun Hp => Hpres2 _ Hp)).
  eapply writable_at_grows; [exact GP0|]. eapply writable_at_grows; [exact GH3|].
  eapply writable_at_grows; [exact GH2|]. eapply writable_at_grows; [exact GH1|]. exact Ha. }
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H WL) mem2) HP2 [0;1;2;3;4;5;6;7;8]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  assert (RKM : forall lo hi, 0x10000 - 3000 <= lo -> hi <= 0x5fc000 + 3000 ->
    forall a, lo <= a < hi -> mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem msP)) a).
  { intros lo hi Hl Hh a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
    [ clear - Ha Hl Hh; lia | intros [] | clear - Ha Hl Hh QSP C1 HSF HES; lia ]. }
  assert (RKS : forall a, spZ regsE - SL_FRAME <= a < spZ regsE ->
    mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem msP)) a).
  { intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
    [ clear - Ha QSP C1 HSF; lia | intros [] | clear - Ha HSF HES; lia ]. }
  repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  rewrite ?(HEI 250%nat ltac:(cbv; lia)), ?(HEI 300%nat ltac:(cbv; lia)), ?(HEI 301%nat ltac:(cbv; lia)),
          ?(HEI 302%nat ltac:(cbv; lia)), ?(HEI 253%nat ltac:(cbv; lia)), ?(HEI 304%nat ltac:(cbv; lia)),
          ?(HEI 305%nat ltac:(cbv; lia)), ?(HEI 298%nat ltac:(cbv; lia)), ?Usp;
  first
  [ intros a Ha; exfalso; clear - Ha; lia
  | intros a Ha; apply RKS; clear - Ha HSF; lia
  | apply RKM; clear - N9 N20 N21 N22 N12 N24 N25 N18 Bcl Bbr Bei Bdd Bmx Bno Bcap Bout; lia
  | intros a Ha _; apply WRc;
    first
    [ (replace a with (rg_send_eintr RG + (a - rg_send_eintr RG)) by (clear - Ha; lia);
       apply Wei; clear - Ha N20; lia)
    | (replace a with (rg_nout RG + (a - rg_nout RG)) by (clear - Ha; lia);
       apply Wno; clear - Ha N12; lia)
    | (replace a with (rg_capout RG + (a - rg_capout RG)) by (clear - Ha; lia);
       apply Wcap; clear - Ha N24; lia)
    | (replace a with (rg_out RG + (a - rg_out RG)) by (clear - Ha; lia);
       apply Wout; clear - Ha N25; lia)
    | (replace a with (rg_client_broken RG + (a - rg_client_broken RG)) by (clear - Ha; lia);
       apply Wbr; clear - Ha N18; lia) ] ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 38)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10.
assert (WRerr : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H WL) mem2) (as_errno B + o))
  by (intros o Ho; apply WRc; exact (Wev o Ho)).
assert (F42 : ew Ea 42 = Z_to_bv 64 (as_errno B))
  by (rewrite <- R10, Herr, <- HERRNO; reflexivity).
assert (BVEa : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
assert (Uspa : base_val Ea (Some 2%nat) = spZ regsE - SL_FRAME)
  by (cbn [base_val]; rewrite (OLDa 2%nat ltac:(clear; lia)); exact Usp).
assert (BA42 : base_val Ea (Some 42%nat) = as_errno B)
  by (cbn [base_val]; rewrite F42; apply unsigned_lit_small; clear - Berr; lia).
(* errno's atom: an int* in the image band, 4-aligned (W_traps.v recipe R1, al2 2: the NONNULL and ALIGN4 checks of
   0x82928 / 0x82930 and 0x82984 are decided) *)
apply (st_ok_pi_add_fact _ _ _ 42%nat (mkAF 0x10000 0x5fc000 2)) in HS;
  [|unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite F42,
    (unsigned_lit_small (as_errno B)) by (clear - Berr; lia);
    change (2 ^ 2) with 4; clear - Berr HERRAL; repeat split; lia].
pose proof sl_errno_apart as (DE2 & DE3 & DE4 & DE5 & DE6 & DE7 & DE8 & DE9).
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 42%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
      rewrite BA42; split; [clear - Berr; lia|]; split; [clear - Berr; lia|];
      split; [|apply Forall_nil]; intros o Ho; cbn [ms_mem restrict]; exact (WRerr o Ho)
    | cbn [ss_mem add_atom]; apply all_disjoint_of_extents; unfold extent_of_region;
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi];
      rewrite BA42, ?(BVEa 250%nat ltac:(cbv; lia)), ?(BVEa 300%nat ltac:(cbv; lia)),
        ?(BVEa 301%nat ltac:(cbv; lia)), ?(BVEa 302%nat ltac:(cbv; lia)),
        ?(BVEa 253%nat ltac:(cbv; lia)), ?(BVEa 304%nat ltac:(cbv; lia)),
        ?(BVEa 305%nat ltac:(cbv; lia)), ?(BVEa 298%nat ltac:(cbv; lia)), ?Uspa;
      cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
      repeat split;
      first [ solve [ clear - Berr QSP C1 HSF; lia ]
            | solve [ clear - DE2 DE3 DE4 DE5 DE6 DE7 DE8 DE9 N9 N20 N21 N22 N12 N24 N25 N18; lia ] ] ].
assert (UB : U Ea BxL = SHADOW_OFF).
{ unfold BxL. rewrite (U_atom Ea 25%nat SB); [reflexivity | | clear; unfold SB; lia].
  rewrite (OLDa 25%nat ltac:(clear; lia)), E25. reflexivity. }
assert (UE42 : U Ea (SOff 42%nat 0) = as_errno B)
  by (apply (U_atom Ea 42%nat); [exact F42 | clear - Berr; lia]).
assert (SHOKa : sh_ok SEGS BxL [mkSHE 42%nat 0 4] Ea (mrestrict (w_H WL) mem2)).
{ constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H WL) mem2 Ea BxL 42%nat (as_errno B) 4 (as_errno B) 0 4).
  - eapply errno_ra. eapply ajournal_gx_AR. exact HJ2.
  - exact UB.
  - exact UE42.
  - clear; lia.
  - clear; lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. clear - Hx Berr UB.
    rewrite <- SB_SHADOW_OFF. unfold SB. lia. }
(* the checks of errno's address (decided), its shadow (decided), errno := EINTR, errno read back and compared with
   EINTR (decided), to the bltu sent, len at 0x829a4 *)
lrun RUN HS HJ2 SHOKa LBspan. { l_awr. } rn msA FA0 GA0.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (BVEb : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ev (Some m) = VAL m)
    by (intros m Hm; cbn [base_val]; rewrite ?ew_ewset_other by (clear - Hm; unfold A_LIM in Hm; lia);
        exact (HEIa m Hm));
  assert (BA42b : base_val Ev (Some 42%nat) = as_errno B)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (repeat match goal with X : _ |- _ => clear X end; lia);
        cbn [base_val] in BA42; exact BA42)
end.
assert (Hs0 : sent = 0)
  by (clear - Hei2 HeiE Hsent; destruct (Z.eq_dec sent 0) as [Hz|Hz];
      [exact Hz | exfalso; pose proof (Hei2 ltac:(lia)); lia]).
assert (F23 : ew Ea 23 = w64 sent) by (rewrite (OLDa 23%nat ltac:(clear; lia)); exact E23).
assert (F8 : ew Ea 8 = w64 len) by (rewrite (OLDa 8%nat ltac:(clear; lia)); exact E8).
psrr_branch_tok RUN BR HS SHOKa LBspan.
2: { exfalso.
  lazymatch type of Hc2 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    assert (G23 : ew Ev 23 = w64 sent) by (rewrite ?ew_ewset_other by (clear; lia); exact F23);
    assert (G8 : ew Ev 8 = w64 len) by (rewrite ?ew_ewset_other by (clear; lia); exact F8);
    rewrite branch_ltu_U, (U_atom Ev 23%nat sent G23), (U_atom Ev 8%nat len G8) in Hc2
      by (clear - Hsent Hlen1; lia)
  end.
  clear - Hc2 Hsent Hs0 Hlen1. apply Z.ltb_ge in Hc2. lia. }
lrun_to RUNTO HS HJ2 SHOKa LBspan A_sl_loop. { l_awr. } rn msT FT0 GT0.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ inG (G_SL B RG) a ->
  ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME) ->
  aview SEGS (w_H WL) (ms_mem msT) a = aview SEGS (w_H WL) memL a).
{ intros a Ha HnG Hsc.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msT) FT0 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msA) FA0 a Ha) by nowr_g HnG.
  rewrite (Hfr2 a Ha ltac:(intros [])) by (clear - Hsc HSF HES; lia).
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msP) FP0 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msH3) FH3 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msH2) FH2 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msH1) FH1 a Ha) by nowr_g HnG.
  reflexivity. }
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (27%bv : bv 5) P27. prreg HS (21%bv : bv 5) P21. prreg HS (26%bv : bv 5) P26.
prreg HS (22%bv : bv 5) P22.
assert (HRL : sl_regsL (ms_regs msT) len line 0).
{ unfold sl_regsL.
  rewrite P8, P9, P23, P24, P25, P27, P21, P26, P22.
  rewrite ?(OLDa 8%nat ltac:(clia)), ?(OLDa 9%nat ltac:(clia)), ?(OLDa 23%nat ltac:(clia)), ?(OLDa 24%nat ltac:(clia)),
    ?(OLDa 25%nat ltac:(clia)).
  rewrite E8, E9, E23, E24, E25, Hs0.
  rewrite !(ew_img _ _ HEIa) by (cbv; lia).
  repeat split; reflexivity. }
assert (HSP2 : spZ (ms_regs msT) = spZ regsE - SL_FRAME).
{ unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp. }
assert (HR3 : getr (ms_regs msT) 3 = getr regsE 3) by (rewrite P3, (OLDa 3%nat ltac:(clia)), E3; exact H3).
assert (HR4 : getr (ms_regs msT) 4 = getr regsE 4) by (rewrite P4, (OLDa 4%nat ltac:(clia)), E4; exact H4).
(* presence and writability survive the round *)
assert (PRall : forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem msT) a).
{ intros a Hp. apply (apresent_grows _ _ _ _ GT0). apply (apresent_grows _ _ _ _ GA0).
  apply Hpres2. apply (apresent_grows _ _ _ _ GP0). apply (apresent_grows _ _ _ _ GH3).
  apply (apresent_grows _ _ _ _ GH2). apply (apresent_grows _ _ _ _ GH1). exact Hp. }
assert (WRall : forall a, writable_at SEGS (arm WL memL) a ->
  writable_at SEGS (mrestrict (w_H WL) (ms_mem msT)) a).
{ intros a Hw. eapply writable_at_grows; [exact GT0|]. eapply writable_at_grows; [exact GA0|].
  apply WRc. exact Hw. }
assert (GLO : forall a, inG (G_SL B RG) a -> 0x10000 <= a < 0x5fc000) by exact sl_inG_img.
(* bytes below alloc_ceiling and outside G_SL, and the frame's bytes, keep their view *)
assert (KLO : forall x, 0 <= x < alloc_ceiling -> ~ inG (G_SL B RG) x ->
  aview SEGS (w_H WL) (ms_mem msT) x = aview SEGS (w_H WL) memL x)
  by (intros x Hx Hg; apply KEEP; [clear - Hx C1; lia | exact Hg | clear - Hx Hceil Hslo WS HSF HES; lia]).
assert (KFR : forall x, spZ regsE - SL_FRAME <= x < spZ regsE ->
  aview SEGS (w_H WL) (ms_mem msT) x = aview SEGS (w_H WL) memL x)
  by (intros x Hx; apply KEEP; [clear - Hx QSP C1 HSF; lia
    | intros Hg; pose proof (GLO x Hg) as HL; clear - Hx HL QSP C1 HSF; lia
    | clear - Hx HSF HES; lia]).
(* the cells, read off the final state's regions: errno, client, eintr, dead, max, nout, capout, out, broken *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF =>
  pose proof (st_ok_pi_region_nth Ev ssF msF 0 _ HS eq_refl) as RG0;
  pose proof (st_ok_pi_region_nth Ev ssF msF 2 _ HS eq_refl) as RG2;
  pose proof (st_ok_pi_region_nth Ev ssF msF 3 _ HS eq_refl) as RG3;
  pose proof (st_ok_pi_region_nth Ev ssF msF 4 _ HS eq_refl) as RG4;
  pose proof (st_ok_pi_region_nth Ev ssF msF 5 _ HS eq_refl) as RG5;
  pose proof (st_ok_pi_region_nth Ev ssF msF 6 _ HS eq_refl) as RG6;
  pose proof (st_ok_pi_region_nth Ev ssF msF 7 _ HS eq_refl) as RG7;
  pose proof (st_ok_pi_region_nth Ev ssF msF 8 _ HS eq_refl) as RG8;
  pose proof (st_ok_pi_region_nth Ev ssF msF 9 _ HS eq_refl) as RG9
end.
cbn [ms_mem restrict] in RG0, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (EB : forall m, (m < 38)%nat -> ew Ev m = ew E m)
    by (intros m Hm; rewrite ?ew_ewset_other by (clear - Hm; lia); exact (OLDa m Hm));
  assert (UI : forall m, (A_TEXT <= m < A_LIM)%nat -> bv_unsigned (ew Ev m) = VAL m)
    by (intros m Hm; rewrite ?ew_ewset_other by (clear - Hm; unfold A_LIM in Hm; lia); exact (HEIa m Hm));
  assert (U42 : bv_unsigned (ew Ev 42) = as_errno B) by exact BA42b;
  assert (WMX : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_send_max RG) 8 mx)
    by (rewrite <- HH22; exact (field_of_region Ev _ (A_HI 22) _ _ _ _ _ _ 1252 8 (SOff 37 0) mx RG5
          (UI 302%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 37%nat ltac:(clia)), E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Hmxr; cbn; lia) ltac:(cbn; lia)));
  assert (WNO : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_nout RG) 8 (no + sent))
    by (replace (rg_nout RG) with (VAL (A_OBJ 12) + 0) by (rewrite Z.add_0_r; exact HV12);
        exact (field_of_region Ev _ (A_OBJ 12) _ _ _ _ _ _ 0 8 (SOff 34 0) (no + sent) RG6
          (UI 253%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 34%nat ltac:(clia)), E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Rn47 HlenO; cbn; lia) ltac:(cbn; lia)));
  assert (WCAP : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_capout RG) 8 capL)
    by (rewrite <- HH24; exact (field_of_region Ev _ (A_HI 24) _ _ _ _ _ _ 1976 8 (SOff 35 0) capL RG7
          (UI 304%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 35%nat ltac:(clia)), E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Rc0 Rc47; cbn; lia) ltac:(cbn; lia)));
  assert (WOUT : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_out RG) 8 outL)
    by (rewrite <- HH25; exact (field_of_region Ev _ (A_HI 25) _ _ _ _ _ _ 2000 8 (SOff 36 0) outL RG8
          (UI 305%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 36%nat ltac:(clia)), E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Ro0 Ro47; cbn; lia) ltac:(cbn; lia)));
  assert (WCL : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_client RG) 4 3)
    by (replace (rg_client RG) with (VAL (A_OBJ 9) + 0) by (rewrite Z.add_0_r; exact HV9);
        exact (field_of_region Ev _ (A_OBJ 9) _ _ _ _ _ _ 0 4 (SLit 3) 3 RG2
          (UI 250%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (WBR : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_client_broken RG) 1 0)
    by (rewrite <- HH18;
        exact (field_of_region Ev _ (A_HI 18) _ _ _ _ _ _ 1212 1 (SLit 0) 0 RG9
          (UI 298%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (WDD : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_send_dead RG) 1 (ct_dd c))
    by (rewrite <- HH21; exact (field_of_region Ev _ (A_HI 21) _ _ _ _ _ _ 1328 1 (SOff 33 0) (ct_dd c) RG4
          (UI 301%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 33%nat ltac:(clia)), E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Hddr; cbn; lia) ltac:(cbn; lia)));
  assert (WEI : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_send_eintr RG) 1 0)
    by (rewrite <- HH20;
        exact (field_of_region Ev _ (A_HI 20) _ _ _ _ _ _ 1372 1 (SLit 0) 0 RG3
          (UI 300%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (WER : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (as_errno B) 4 4)
    by (replace (as_errno B) with (as_errno B + 0) at 1 by (apply Z.add_0_r);
        exact (field_of_region Ev _ 42 _ _ _ _ _ _ 0 4 (SLit 4) 4 RG0
          U42 (or_introl eq_refl) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)))
end.
(* the line, the g_out block and the read-only bytes lie below alloc_ceiling and outside G_SL *)
assert (GL2 : garr8 SEGS (arm WL (ms_mem msT)) line (bzs Bl)).
{ apply (garr8_keep WL memL (ms_mem msT)); [|exact HGL].
  intros x Hx. unfold bzs in Hx. rewrite length_map in Hx. change (Z.of_nat (length Bl)) with len in Hx.
  apply KLO; [|exact (HLG x Hx)].
  destruct HLOK as [HL0 | [(q & m & Hqm & _ & Hq1 & Hq2) | (HIr & _ & _)]];
    [clear - HL0 Hlen1; lia | |].
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL q m HARL Hqm) as (_ & _ & Hpc & _).
    clear - Hx Hq1 Hq2 Hpc Hline0. lia.
  - pose proof (pa_img_range _ (HIr x Hx)) as HXI. clear - HXI C1. lia. }
assert (ROM2 : rom_view SEGS WL (ms_mem msT)).
{ intros a Ha. rewrite KLO; [exact (HROM a Ha) | | intros Hg; exact (HGR a Hg Ha)].
  destruct Ha as (sg & Hsg & _ & Hr).
  assert (HIa : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range _ HIa) as HXI. clear - HXI C1. lia. }
assert (BLK2 : (capL = 0 /\ outL = 0 /\ no + sent = 0) \/
  (0 < capL /\ no + sent <= capL /\ In (outL, capL) (ablocks B lyL SL) /\
   exists junk, Z.of_nat (length junk) = capL - (no + sent) /\
     garr8 SEGS (arm WL (ms_mem msT)) outL (bzs ((O ++ firstn (Z.to_nat sent) Bl) ++ junk)))).
{ destruct Hblk as [Hb0 | (Hbc & Hbn & Hbi & junk & Hbj & Hbg)]; [left; exact Hb0 | right].
  split; [exact Hbc|]. split; [exact Hbn|]. split; [exact Hbi|].
  exists junk. split; [exact Hbj|].
  apply (garr8_keep WL memL (ms_mem msT)); [|exact Hbg].
  destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hbi) as (_ & _ & Hpc & _).
  assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  destruct (al_client_img _ _ LAWS lyL SL WL memL mdL x HARL) as (_ & Himg).
  { left. exists outL, capL. split; [exact Hbi|]. rewrite Hrq. clear - Hx Hbj HlenO. lia. }
  apply KLO; [clear - Hx Hbj HlenO Hpc Hrq Ro0 C1; lia|].
  intros HgX. exact (Himg (proj1 (HG x HgX))). }
(* ---- the back edge: SLI at the new head with sent = 0, g_send_eintr = 0, errno = EINTR ---- *)
assert (Hci : ct_ei c = 1) by (clear - Hei1 HeiE; lia).
assert (HEV : (if (ct_ei c =? 1) && (0 =? 0) then send_line_c.EINTR_V else ct_ev c) = 4)
  by (rewrite Hci; reflexivity).
clear U23. subst sent.
apply (IH regsE ly S W mem md c O mx no cap out line Bl WL (ms_regs msT) (ms_mem msT) _ 0 0).
2: { clear - Hb HeiE. unfold len in Hb. rewrite Nat2Z.inj_succ in Hb. lia. }
unfold SLI. cbv zeta.
exists lyL, SL, kL, (if (ct_ei c =? 1) && (0 =? 0) then send_line_c.EINTR_V else ct_ev c), capL, outL, spent, rest.
split; [exact HJ2|]. split; [exact HSP2|]. split; [exact HR3|]. split; [exact HR4|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|]. split; [exact HRL|].
split.
{ destruct HSP as (M0 & M8 & M16 & M24 & M32).
  split; [|split; [|split; [|split]]];
  (apply (vm_keep WL memL (ms_mem msT)); [intros x Hx; apply KFR; clear - Hx HSF; lia | assumption]). }
split; [intros i Hi; apply (vm_keep WL memL (ms_mem msT));
  [intros x Hx; apply KFR; clear - Hx Hi HSF; lia | exact (HSV i Hi)]|].
split; [exact Hcl|]. split; [exact Hbr|]. split; [clear - Hlen1; lia|].
split; [right; reflexivity|]. split; [intros _; reflexivity|]. split; [intros _; reflexivity|].
split; [reflexivity|].
split.
{ unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev]. rewrite HEV.
  split; [exact WMX|]. split; [intros i Hi; apply WRall; exact (Wmx i Hi)|].
  split; [exact WNO|]. split; [intros i Hi; apply WRall; exact (Wno i Hi)|].
  split; [exact WCAP|]. split; [intros i Hi; apply WRall; exact (Wcap i Hi)|].
  split; [exact WOUT|]. split; [intros i Hi; apply WRall; exact (Wout i Hi)|].
  split; [exact WCL|]. split; [intros i Hi; apply WRall; exact (Wcl i Hi)|].
  split; [exact WBR|]. split; [intros i Hi; apply WRall; exact (Wbr i Hi)|].
  split; [exact WDD|]. split; [intros i Hi; apply WRall; exact (Wdd i Hi)|].
  split; [exact WEI|]. split; [intros i Hi; apply WRall; exact (Wei i Hi)|].
  split; [exact WER|]. split; [intros i Hi; apply WRall; exact (Wev i Hi)|].
  split; [clear; lia|].
  split; [left; reflexivity|]. split; [left; reflexivity|]. split; [exact Hddr|]. split; [left; reflexivity|].
  split; [exact Hmxr|]. split; [exact HlenO|].
  exact BLK2. }
split; [exact GL2|]. split; [exact Hline0|]. split; [exact Hline1|]. split; [exact ROM2|].
split; [exact HLOK|]. split; [exact HLG|]. split; [exact Hcapq|]. split; [exact Hdd2|].
split; [exact HMM|]. split; [exact HLM|].
split; [intros a Ha1 Ha2 Ha3 Hp; apply PRall; exact (HAPK a Ha1 Ha2 Ha3 Hp)|].
split; [exact HMOK|]. split; [exact HMLE|]. split; [exact HCOST|]. split; [exact Hspent0|].
split; [exact HPerm0|]. split; [exact HPerm1|]. exact HFR.
Qed.

(* send_line's dead round: g_send_eintr = 0, g_send_dead <> 0 (then sent = 0): errno := EPIPE (its NONNULL / ALIGN4
   checks 0x8295c / 0x82964 and the read-back checks 0x82984 / 0x82988 decided by the seated errno atom), errno read
   back (EPIPE <> EINTR, decided), g_client_broken := 1 (0x82a94), the epilogue X *)
Lemma sl_arm_dead : forall regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL -> eiL = 0 -> ct_dd c = 1 ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hdd.
(* ---- round prelude (begin) ---- *)
sl_intro HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & HstkL & _).
pose proof HstkL as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresL.
assert (WS : SL_STK = 16528) by reflexivity.
assert (HSF : SL_FRAME = 144) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev, Hclr, Hbrr, Hddr, Heir.
assert (Rcapout : 0 <= capL /\ 0 <= outL /\ no + sent <= 2 ^ 47 /\ capL <= 2 ^ 47 /\ outL <= 2 ^ 47).
{ destruct Hblk as [(Hz0 & Hz1 & Hz2) | (Hz3 & Hz4 & Hin1 & _)]; [repeat split; lia|].
  destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hin1) as (_ & Hp4 & Hpc & _).
  assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
  rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
assert (Hlen1 : 1 <= len <= 2 ^ 63 - 1) by lia.
assert (Hline4 : 4096 <= line).
{ destruct HLOK as [H0 | [(q & m & Hin & _ & Hq & _) | (Himg & _ & _)]]; [lia | |].
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL q m HARL Hin) as (_ & H4096 & _); lia.
  - pose proof (pa_img_range line (Himg line ltac:(lia))); lia. }
pose proof (sl_loop_entry lyL SL WL regsL memL (spZ regsE) len line sent eiL (ct_dd c)
  (no + sent) capL outL mx evL (O ++ firstn (Z.to_nat sent) Bl)
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR Hlen1 ltac:(lia) ltac:(lia)
  HSP HOUT ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
pose proof sl_bands as (Bcl & Bbr & Bei & Bdd & Bmx & Bno & Bcap & Bout & Berr).
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0 WS; lia).
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R23 & R24 & R25 & R27 & R21 & R26 & R22).
remember (Eimg (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsL 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact R9).
assert (E23 : ew E 23 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = w64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = w64 (ct_dd c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = w64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = w64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = w64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (NALL : VAL 252%nat = rg_send_eintr RG /\ VAL 253%nat = rg_nout RG /\ VAL 298%nat + 1212 = rg_client_broken RG /\
  VAL 300%nat + 1372 = rg_send_eintr RG /\ VAL 303%nat + 1372 = rg_nout RG /\ VAL 304%nat + 1976 = rg_capout RG /\
  VAL 305%nat + 2000 = rg_out RG)
  by (repeat split; first [exact HV11 | exact HV12 | exact HH18 | exact HH20 | exact HH23 | exact HH24 | exact HH25]).
assert (N9 : VAL 250%nat = rg_client RG) by exact HV9.
assert (N11 : VAL 252%nat = rg_send_eintr RG) by exact HV11.
assert (N12 : VAL 253%nat = rg_nout RG) by exact HV12.
assert (N18 : VAL 298%nat + 1212 = rg_client_broken RG) by exact HH18.
assert (N20 : VAL 300%nat + 1372 = rg_send_eintr RG) by exact HH20.
assert (N21 : VAL 301%nat + 1328 = rg_send_dead RG) by exact HH21.
assert (N22 : VAL 302%nat + 1252 = rg_send_max RG) by exact HH22.
assert (N23 : VAL 303%nat + 1372 = rg_nout RG) by exact HH23.
assert (N24 : VAL 304%nat + 1976 = rg_capout RG) by exact HH24.
assert (N25 : VAL 305%nat + 2000 = rg_out RG) by exact HH25.
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WL) memL)) by constructor.
assert (U9 : U E (SOff 9 0) = line) by (apply U_atom; [exact E9 | lia]).
assert (U23 : U E (SOff 23 0) = sent) by (apply U_atom; [exact E23 | lia]).
assert (UADD : U E (SAlu ALU_ADD (SOff 9 0) (SOff 23 0)) = line + sent)
  by (apply (trap_U_add E _ _ line sent U9 U23); lia).
(* 0x828f8 add s2,s1,s7; 0x828fc PTR_BLTU bltu s2,s1 -> unimp *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH1 FH1 GH1.
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite (trap_ptr_bltu E (SOff 9 0) (SAlu ALU_ADD (SOff 9 0) (SOff 23 0)) line (line + sent) U9 UADD
    ltac:(lia)) in Hc. discriminate Hc. }
(* 0x82900 seqz; xor s8; 0x82908 NULL_XOR beqz -> unimp *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH2 FH2 GH2.
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite (trap_null_xor_folded E 24 E24) in Hc0. discriminate Hc0. }
(* the g_client test (bne g_client, 3 -> abort: decided, g_client is 3), the load of g_send_eintr, to its beqz *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH3 FH3 GH3.
(* ---- round prelude (end) ---- *)
psrr_branch_tok RUN BR HS SHOK LBspan.
2: { exfalso. rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc1 by (clear - Heir; lia).
  apply Z.eqb_neq in Hc1. lia. }
(* g_send_eintr = 0: ld a0,32(sp); lbu g_send_dead; beqz -> the data round (refuted: g_send_dead is 1) *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msD FD0 GD0.
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite branch_eq_U, (U_atom E 33 (ct_dd c) E33), (U_lit E 0) in Hc2 by (clear - Hddr; lia).
  rewrite Hdd in Hc2. vm_compute in Hc2. discriminate Hc2. }
(* g_send_dead <> 0: to the jal __errno_location at 0x82958 *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msP FP0 GP0.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_SL B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
    (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
    WL (ms_regs msP) (ms_mem msP) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out))
    ly S W mem md ([] : list (Z * Z)) lyL SL _ kL (- SL_FRAME) (Z_to_bv 64 (BASE + 1560)) HG eq_refl HJ).
  - unfold spZ at 1. rewrite Q2, Usp. clear. unfold SL_FRAME. lia.
  - unfold SL_FRAME. reflexivity.
  - unfold SL_FRAME. clear. lia.
  - clear. lia.
  - clear. vm_compute. intros Hx. discriminate Hx.
  - rewrite Q3, E3, H3. exact Hgp.
  - rewrite Q4, E4, H4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros _. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE _. exact (AERRNO lyL SL WL (ms_regs msP) (ms_mem msP) _ HPRE). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
assert (WRc : forall a, writable_at SEGS (arm WL memL) a -> writable_at SEGS (mrestrict (w_H WL) mem2) a).
{ intros a Ha. apply (writable_kept (w_H WL) (ms_mem msP) mem2 a (fun Hp => Hpres2 _ Hp)).
  eapply writable_at_grows; [exact GP0|]. eapply writable_at_grows; [exact GD0|].
  eapply writable_at_grows; [exact GH3|].
  eapply writable_at_grows; [exact GH2|]. eapply writable_at_grows; [exact GH1|]. exact Ha. }
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H WL) mem2) HP2 [0;1;2;3;4;5;6;7;8]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  assert (RKM : forall lo hi, 0x10000 - 3000 <= lo -> hi <= 0x5fc000 + 3000 ->
    forall a, lo <= a < hi -> mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem msP)) a).
  { intros lo hi Hl Hh a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
    [ clear - Ha Hl Hh; lia | intros [] | clear - Ha Hl Hh QSP C1 HSF HES; lia ]. }
  assert (RKS : forall a, spZ regsE - SL_FRAME <= a < spZ regsE ->
    mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem msP)) a).
  { intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
    [ clear - Ha QSP C1 HSF; lia | intros [] | clear - Ha HSF HES; lia ]. }
  repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  rewrite ?(HEI 250%nat ltac:(cbv; lia)), ?(HEI 252%nat ltac:(cbv; lia)), ?(HEI 300%nat ltac:(cbv; lia)),
          ?(HEI 301%nat ltac:(cbv; lia)),
          ?(HEI 302%nat ltac:(cbv; lia)), ?(HEI 253%nat ltac:(cbv; lia)), ?(HEI 304%nat ltac:(cbv; lia)),
          ?(HEI 305%nat ltac:(cbv; lia)), ?(HEI 298%nat ltac:(cbv; lia)), ?Usp;
  first
  [ intros a Ha; exfalso; clear - Ha; lia
  | intros a Ha; apply RKS; clear - Ha HSF; lia
  | apply RKM; clear - N9 N11 N20 N21 N22 N12 N24 N25 N18 Bcl Bbr Bei Bdd Bmx Bno Bcap Bout; lia
  | intros a Ha _; apply WRc;
    first
    [ (replace a with (rg_send_eintr RG + (a - rg_send_eintr RG)) by (clear - Ha; lia);
       apply Wei; clear - Ha N11 N20; lia)
    | (replace a with (rg_nout RG + (a - rg_nout RG)) by (clear - Ha; lia);
       apply Wno; clear - Ha N12; lia)
    | (replace a with (rg_capout RG + (a - rg_capout RG)) by (clear - Ha; lia);
       apply Wcap; clear - Ha N24; lia)
    | (replace a with (rg_out RG + (a - rg_out RG)) by (clear - Ha; lia);
       apply Wout; clear - Ha N25; lia)
    | (replace a with (rg_client_broken RG + (a - rg_client_broken RG)) by (clear - Ha; lia);
       apply Wbr; clear - Ha N18; lia) ] ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 38)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10.
assert (WRerr : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H WL) mem2) (as_errno B + o))
  by (intros o Ho; apply WRc; exact (Wev o Ho)).
assert (F42 : ew Ea 42 = Z_to_bv 64 (as_errno B))
  by (rewrite <- R10, Herr, <- HERRNO; reflexivity).
assert (BVEa : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
assert (Uspa : base_val Ea (Some 2%nat) = spZ regsE - SL_FRAME)
  by (cbn [base_val]; rewrite (OLDa 2%nat ltac:(clear; lia)); exact Usp).
assert (BA42 : base_val Ea (Some 42%nat) = as_errno B)
  by (cbn [base_val]; rewrite F42; apply unsigned_lit_small; clear - Berr; lia).
(* errno's atom: an int* in the image band, 4-aligned (W_traps.v recipe R1, al2 2: the NONNULL and ALIGN4 checks of
   0x8295c / 0x82964 and 0x82984 are decided) *)
apply (st_ok_pi_add_fact _ _ _ 42%nat (mkAF 0x10000 0x5fc000 2)) in HS;
  [|unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite F42,
    (unsigned_lit_small (as_errno B)) by (clear - Berr; lia);
    change (2 ^ 2) with 4; clear - Berr HERRAL; repeat split; lia].
pose proof sl_errno_apart as (DE2 & DE3 & DE4 & DE5 & DE6 & DE7 & DE8 & DE9).
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 42%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
      rewrite BA42; split; [clear - Berr; lia|]; split; [clear - Berr; lia|];
      split; [|apply Forall_nil]; intros o Ho; cbn [ms_mem restrict]; exact (WRerr o Ho)
    | cbn [ss_mem add_atom]; apply all_disjoint_of_extents; unfold extent_of_region;
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi];
      rewrite BA42, ?(BVEa 250%nat ltac:(cbv; lia)), ?(BVEa 252%nat ltac:(cbv; lia)), ?(BVEa 300%nat ltac:(cbv; lia)),
        ?(BVEa 301%nat ltac:(cbv; lia)), ?(BVEa 302%nat ltac:(cbv; lia)),
        ?(BVEa 253%nat ltac:(cbv; lia)), ?(BVEa 304%nat ltac:(cbv; lia)),
        ?(BVEa 305%nat ltac:(cbv; lia)), ?(BVEa 298%nat ltac:(cbv; lia)), ?Uspa;
      cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
      repeat split;
      first [ solve [ clear - Berr QSP C1 HSF; lia ]
            | solve [ clear - DE2 DE3 DE4 DE5 DE6 DE7 DE8 DE9 N9 N11 N20 N21 N22 N12 N24 N25 N18; lia ] ] ].
assert (UB : U Ea BxL = SHADOW_OFF).
{ unfold BxL. rewrite (U_atom Ea 25%nat SB); [reflexivity | | clear; unfold SB; lia].
  rewrite (OLDa 25%nat ltac:(clear; lia)), E25. reflexivity. }
assert (UE42 : U Ea (SOff 42%nat 0) = as_errno B)
  by (apply (U_atom Ea 42%nat); [exact F42 | clear - Berr; lia]).
assert (SHOKa : sh_ok SEGS BxL [mkSHE 42%nat 0 4] Ea (mrestrict (w_H WL) mem2)).
{ constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H WL) mem2 Ea BxL 42%nat (as_errno B) 4 (as_errno B) 0 4).
  - eapply errno_ra. eapply ajournal_gx_AR. exact HJ2.
  - exact UB.
  - exact UE42.
  - clear; lia.
  - clear; lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. clear - Hx Berr UB.
    rewrite <- SB_SHADOW_OFF. unfold SB. lia. }
(* the checks of errno's address (decided), its shadow (decided), errno := EPIPE, errno read back and compared with
   EINTR (decided: EPIPE), g_client_broken := 1, to the epilogue at 0x82aa0 *)
lrun_to RUNTO HS HJ2 SHOKa LBspan A_sl_epi. { l_awr. } rn msT FT0 GT0.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ inG (G_SL B RG) a ->
  ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME) ->
  aview SEGS (w_H WL) (ms_mem msT) a = aview SEGS (w_H WL) memL a).
{ intros a Ha HnG Hsc.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msT) FT0 a Ha) by nowr_g HnG.
  rewrite (Hfr2 a Ha ltac:(intros [])) by (clear - Hsc HSF HES; lia).
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msP) FP0 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msD) FD0 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msH3) FH3 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msH2) FH2 a Ha) by nowr_g HnG.
  rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msH1) FH1 a Ha) by nowr_g HnG.
  reflexivity. }
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
(* presence and writability survive the round *)
assert (PRall : forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem msT) a).
{ intros a Hp. apply (apresent_grows _ _ _ _ GT0).
  apply Hpres2. apply (apresent_grows _ _ _ _ GP0). apply (apresent_grows _ _ _ _ GD0).
  apply (apresent_grows _ _ _ _ GH3).
  apply (apresent_grows _ _ _ _ GH2). apply (apresent_grows _ _ _ _ GH1). exact Hp. }
assert (WRall : forall a, writable_at SEGS (arm WL memL) a ->
  writable_at SEGS (mrestrict (w_H WL) (ms_mem msT)) a).
{ intros a Hw. eapply writable_at_grows; [exact GT0|]. apply WRc. exact Hw. }
assert (GLO : forall a, inG (G_SL B RG) a -> 0x10000 <= a < 0x5fc000) by exact sl_inG_img.
assert (KLO : forall x, 0 <= x < alloc_ceiling -> ~ inG (G_SL B RG) x ->
  aview SEGS (w_H WL) (ms_mem msT) x = aview SEGS (w_H WL) memL x)
  by (intros x Hx Hg; apply KEEP; [clear - Hx C1; lia | exact Hg | clear - Hx Hceil Hslo WS HSF HES; lia]).
assert (KFR : forall x, spZ regsE - SL_FRAME <= x < spZ regsE ->
  aview SEGS (w_H WL) (ms_mem msT) x = aview SEGS (w_H WL) memL x)
  by (intros x Hx; apply KEEP; [clear - Hx QSP C1 HSF; lia
    | intros Hg; pose proof (GLO x Hg) as HL; clear - Hx HL QSP C1 HSF; lia
    | clear - Hx HSF HES; lia]).
(* the cells, read off the final state's regions: errno, client, eintr, dead, max, nout, capout, out, broken *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF =>
  pose proof (st_ok_pi_region_nth Ev ssF msF 0 _ HS eq_refl) as RG0;
  pose proof (st_ok_pi_region_nth Ev ssF msF 2 _ HS eq_refl) as RG2;
  pose proof (st_ok_pi_region_nth Ev ssF msF 3 _ HS eq_refl) as RG3;
  pose proof (st_ok_pi_region_nth Ev ssF msF 4 _ HS eq_refl) as RG4;
  pose proof (st_ok_pi_region_nth Ev ssF msF 5 _ HS eq_refl) as RG5;
  pose proof (st_ok_pi_region_nth Ev ssF msF 6 _ HS eq_refl) as RG6;
  pose proof (st_ok_pi_region_nth Ev ssF msF 7 _ HS eq_refl) as RG7;
  pose proof (st_ok_pi_region_nth Ev ssF msF 8 _ HS eq_refl) as RG8;
  pose proof (st_ok_pi_region_nth Ev ssF msF 9 _ HS eq_refl) as RG9
end.
cbn [ms_mem restrict] in RG0, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (EB : forall m, (m < 38)%nat -> ew Ev m = ew E m)
    by (intros m Hm; rewrite ?ew_ewset_other by (clear - Hm; lia); exact (OLDa m Hm));
  assert (UI : forall m, (A_TEXT <= m < A_LIM)%nat -> bv_unsigned (ew Ev m) = VAL m)
    by (intros m Hm; rewrite ?ew_ewset_other by (clear - Hm; unfold A_LIM in Hm; lia); exact (HEIa m Hm));
  assert (U42 : bv_unsigned (ew Ev 42) = as_errno B)
    by (rewrite ?ew_ewset_other by clia; cbn [base_val] in BA42; exact BA42);
  assert (WMX : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_send_max RG) 8 mx)
    by (rewrite <- HH22; exact (field_of_region Ev _ (A_HI 22) _ _ _ _ _ _ 1252 8 (SOff 37 0) mx RG5
          (UI 302%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 37%nat ltac:(clia)), E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Hmxr; cbn; lia) ltac:(cbn; lia)));
  assert (WNO : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_nout RG) 8 (no + sent))
    by (replace (rg_nout RG) with (VAL (A_OBJ 12) + 0) by (rewrite Z.add_0_r; exact HV12);
        exact (field_of_region Ev _ (A_OBJ 12) _ _ _ _ _ _ 0 8 (SOff 34 0) (no + sent) RG6
          (UI 253%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 34%nat ltac:(clia)), E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Rn47 HlenO; cbn; lia) ltac:(cbn; lia)));
  assert (WCAP : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_capout RG) 8 capL)
    by (rewrite <- HH24; exact (field_of_region Ev _ (A_HI 24) _ _ _ _ _ _ 1976 8 (SOff 35 0) capL RG7
          (UI 304%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 35%nat ltac:(clia)), E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Rc0 Rc47; cbn; lia) ltac:(cbn; lia)));
  assert (WOUT : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_out RG) 8 outL)
    by (rewrite <- HH25; exact (field_of_region Ev _ (A_HI 25) _ _ _ _ _ _ 2000 8 (SOff 36 0) outL RG8
          (UI 305%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 36%nat ltac:(clia)), E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Ro0 Ro47; cbn; lia) ltac:(cbn; lia)));
  assert (WCL : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_client RG) 4 3)
    by (replace (rg_client RG) with (VAL (A_OBJ 9) + 0) by (rewrite Z.add_0_r; exact HV9);
        exact (field_of_region Ev _ (A_OBJ 9) _ _ _ _ _ _ 0 4 (SLit 3) 3 RG2
          (UI 250%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (WBR : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_client_broken RG) 1 1)
    by (rewrite <- HH18;
        exact (field_of_region Ev _ (A_HI 18) _ _ _ _ _ _ 1212 1 (SLit 1) 1 RG9
          (UI 298%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (WDD : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_send_dead RG) 1 (ct_dd c))
    by (rewrite <- HH21; exact (field_of_region Ev _ (A_HI 21) _ _ _ _ _ _ 1328 1 (SOff 33 0) (ct_dd c) RG4
          (UI 301%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 33%nat ltac:(clia)), E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Hddr; cbn; lia) ltac:(cbn; lia)));
  assert (WEI : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (rg_send_eintr RG) 1 eiL)
    by (replace (rg_send_eintr RG) with (VAL (A_OBJ 11) + 0) by (rewrite Z.add_0_r; exact HV11);
        exact (field_of_region Ev _ (A_OBJ 11) _ _ _ _ _ _ 0 1 (SOff 32 0) eiL RG3
          (UI 252%nat ltac:(cbv; lia)) (or_introl eq_refl)
          ltac:(cbn [sv_denot]; rewrite (EB 32%nat ltac:(clia)), E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(clear - Heir; cbn; lia) ltac:(cbn; lia)));
  assert (WER : val_mem SEGS (mrestrict (w_H WL) (ms_mem msT)) (as_errno B) 4 32)
    by (replace (as_errno B) with (as_errno B + 0) at 1 by (apply Z.add_0_r);
        exact (field_of_region Ev _ 42 _ _ _ _ _ _ 0 4 (SLit 32) 32 RG0
          U42 (or_introl eq_refl) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)))
end.
assert (Hs0 : sent = 0) by exact (Hdd1 Hdd).
destruct (Hdd2 Hdd) as [HcapL HoutL].
(* the g_out block's bytes lie below alloc_ceiling and outside G_SL *)
assert (BLK2 : (cap = 0 /\ out = 0 /\ no = 0) \/
  (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B lyL SL) /\
   exists junk, Z.of_nat (length junk) = cap - no /\
     garr8 SEGS (arm WL (ms_mem msT)) out (bzs (O ++ junk)))).
{ rewrite Hs0, HcapL, HoutL in Hblk. change (Z.to_nat 0) with 0%nat in Hblk.
  rewrite firstn_O, app_nil_r, Z.add_0_r in Hblk.
  rewrite Hs0 in HlenO. change (Z.to_nat 0) with 0%nat in HlenO. rewrite firstn_O, app_nil_r, Z.add_0_r in HlenO.
  destruct Hblk as [Hb0 | (Hbc & Hbn & Hbi & junk & Hbj & Hbg)]; [left; exact Hb0 | right].
  split; [exact Hbc|]. split; [exact Hbn|]. split; [exact Hbi|].
  exists junk. split; [exact Hbj|].
  apply (garr8_keep WL memL (ms_mem msT)); [|exact Hbg].
  destruct (al_blocks _ _ LAWS lyL SL WL memL mdL out cap HARL Hbi) as (_ & _ & Hpc & _).
  assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  destruct (al_client_img _ _ LAWS lyL SL WL memL mdL x HARL) as (_ & Himg).
  { left. exists out, cap. split; [exact Hbi|]. rewrite Hrq. clear - Hx Hbj HlenO. lia. }
  apply KLO; [clear - Hx Hbj HlenO Hpc Hrq Ro0 HoutL C1; lia|].
  intros HgX. exact (Himg (proj1 (HG x HgX))). }
assert (HCTL : sl_ctl c len = CTL 3 1 1 0 32).
{ rewrite (sl_ctl_on c len Hcl Hbr ltac:(clear - Hlen1; lia)), Hdd. reflexivity. }
change (BASE + 1884) with (BASE + A_sl_epi).
apply (sl_exit regsE ly S W mem md c O mx no cap out Bl lyL SL WL (ms_regs msT) (ms_mem msT) _ kL out rest HJ2).
- unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp.
- rewrite P3, (OLDa 3%nat ltac:(clia)), E3. exact H3.
- rewrite P4, (OLDa 4%nat ltac:(clia)), E4. exact H4.
- exact HraE.
- intros i Hi. apply (vm_keep WL memL (ms_mem msT)); [|exact (HSV i Hi)].
  intros x Hx. apply KFR. clear - Hx Hi HSF. lia.
- intros a Ha1 Ha2 Ha3 Hp. apply PRall. exact (HAPK a Ha1 Ha2 Ha3 Hp).
- unfold sl_cost. rewrite (sl_live_false_dead c _ Hdd). rewrite <- (Hspent0 Hdd). exact HMLE.
- exact HPerm0.
- rewrite (sl_cap_dead c mx no cap _ Hdd). rewrite <- HcapL, <- HoutL. exact HPerm1.
- change (Z.of_nat (length Bl)) with len.
  rewrite HCTL, (sl_O_dead c O Bl Hdd), (sl_no_dead c no _ Hdd), (sl_cap_dead c mx no cap _ Hdd).
  rewrite Hs0, Z.add_0_r in WNO. rewrite HcapL in WCAP. rewrite HoutL in WOUT. rewrite Hdd in WDD.
  rewrite Hei0 in WEI.
  rewrite Hs0 in HlenO. change (Z.to_nat 0) with 0%nat in HlenO. rewrite firstn_O, app_nil_r, Z.add_0_r in HlenO.
  unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [exact WMX|]. split; [intros i Hi; apply WRall; exact (Wmx i Hi)|].
  split; [exact WNO|]. split; [intros i Hi; apply WRall; exact (Wno i Hi)|].
  split; [exact WCAP|]. split; [intros i Hi; apply WRall; exact (Wcap i Hi)|].
  split; [exact WOUT|]. split; [intros i Hi; apply WRall; exact (Wout i Hi)|].
  split; [exact WCL|]. split; [intros i Hi; apply WRall; exact (Wcl i Hi)|].
  split; [exact WBR|]. split; [intros i Hi; apply WRall; exact (Wbr i Hi)|].
  split; [exact WDD|]. split; [intros i Hi; apply WRall; exact (Wdd i Hi)|].
  split; [exact WEI|]. split; [intros i Hi; apply WRall; exact (Wei i Hi)|].
  split; [exact WER|]. split; [intros i Hi; apply WRall; exact (Wev i Hi)|].
  split; [clear; lia|].
  split; [left; reflexivity|]. split; [right; reflexivity|]. split; [right; reflexivity|]. split; [left; reflexivity|].
  split; [exact Hmxr|]. split; [exact HlenO|].
  exact BLK2.
- intros _. reflexivity.
Qed.

(* ---- The data round's helpers (image A's lib/A/W_send_line_loop.v sl_canon / l_cells / l_vals, B's regions). ---- *)
(* A state at N (0x829cc) with s3 = n and a1 forgotten: the three ways the n computation reaches it, made one. *)
Lemma sl_canon : forall E ss ms (v19 v11 : word) nf,
st_ok_pi SEGS VAL E ss ms -> YP07.ss_atoms_p (YP07.pband 38 A_TEXT) ss = true ->
getr (ms_regs ms) 19%bv = v19 -> getr (ms_regs ms) 11%bv = v11 ->
afact_ok (havoc E 38 [v19; v11]) 38 nf ->
st_ok_pi SEGS VAL (havoc E 38 [v19; v11])
  (add_atom (mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) 19%bv (SOff 38 0)) 11%bv (SOff 39 0)) (ss_mem ss) (ss_resv ss)
     (mkFacts (f_atoms (ss_facts ss)) [] [])) 38 nf) ms.
Proof.
intros E ss ms v19 v11 nf HS Hat H19 H11 Hf.
pose proof (st_ok_pi_havoc 38 E ss ms [v19; v11] HS Hat ltac:(cbn; unfold A_TEXT; lia)) as H1.
assert (D38 : sv_denot (havoc E 38 [v19; v11]) (SOff 38 0) = v19)
  by (cbn [sv_denot]; unfold havoc; cbn [ew]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (D39 : sv_denot (havoc E 38 [v19; v11]) (SOff 39 0) = v11)
  by (cbn [sv_denot]; unfold havoc; cbn [ew]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
pose proof (ast_ok_pi_set_reg_fp _ _ _ 19%bv (SOff 38 0) H1 eq_refl ltac:(rewrite D38; symmetry; exact H19)) as H2.
pose proof (ast_ok_pi_set_reg_fp _ _ _ 11%bv (SOff 39 0) H2 eq_refl ltac:(rewrite D39; symmetry; exact H11)) as H3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H3.
pose proof (st_ok_pi_facts_incl3 _ _ _ (f_atoms (ss_facts ss)) [] [] H3) as H4.
cbn [ss_facts set_facts ss_pc ss_regs ss_mem ss_resv] in H4.
apply st_ok_pi_add_fact; [|exact Hf].
apply H4; intros x Hx; [exact Hx | destruct Hx | destruct Hx].
Qed.

(* the write windows of the loop head's regions, as cells *)
Definition l_cells (a : Z) : Prop :=
(rg_send_eintr RG <= a < rg_send_eintr RG + 1) \/ (rg_nout RG <= a < rg_nout RG + 8) \/
(rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8) \/
(rg_client_broken RG <= a < rg_client_broken RG + 1).
Lemma l_cells_dec : forall a, l_cells a \/ ~ l_cells a.
Proof. intros a. unfold l_cells. lia. Qed.
Lemma l_wrange_cells : forall E a, img_env VAL A_LIM E -> in_wrange E l_regions a -> l_cells a.
Proof.
intros E a HEI (rr & Hin & Hr). unfold l_regions in Hin. cbn [In] in Hin.
pose proof (HEI (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U11.
pose proof (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U12.
pose proof (HEI (A_HI 24) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U24.
pose proof (HEI (A_HI 25) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U25.
pose proof (HEI (A_HI 18) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U18.
pose proof (HEI (A_HI 21) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U21.
pose proof (HEI (A_HI 22) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U22.
pose proof (HEI (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U9.
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi r_frame r_client r_eintr r_dead r_max r_nout r_capout r_out r_broken base_val] in Hr;
    rewrite ?U11, ?U12, ?U24, ?U25, ?U18, ?U21, ?U22, ?U9 in Hr;
    first [ exfalso; clear - Hr; lia
          | unfold l_cells; rewrite ?HV11, ?HV12 in Hr; clear - Hr HH24 HH25 HH18; lia ] | ]).
destruct Hin.
Qed.
(* the five cells read off a state whose regions are the loop head's *)
Lemma l_vals : forall Ex ss ms ei nov capv outv,
st_ok_pi SEGS VAL Ex ss ms -> ss_mem ss = l_regions -> img_env VAL A_LIM Ex ->
ew Ex 32 = w64 ei -> ew Ex 34 = w64 nov -> ew Ex 35 = w64 capv -> ew Ex 36 = w64 outv ->
0 <= ei < 2 ^ 8 -> 0 <= nov < 2 ^ 64 -> 0 <= capv < 2 ^ 64 -> 0 <= outv < 2 ^ 64 ->
val_mem SEGS (ms_mem ms) (rg_send_eintr RG) 1 ei /\ val_mem SEGS (ms_mem ms) (rg_nout RG) 8 nov /\
val_mem SEGS (ms_mem ms) (rg_capout RG) 8 capv /\ val_mem SEGS (ms_mem ms) (rg_out RG) 8 outv /\
val_mem SEGS (ms_mem ms) (rg_client_broken RG) 1 0.
Proof.
intros Ex ss ms ei nov capv outv HS Hm HEI E32 E34 E35 E36 R1 R2 R3 R4.
assert (RN : forall i r, nth_error l_regions i = Some r -> region_ok SEGS Ex (ms_mem ms) r)
  by (intros i r Hi; apply (st_ok_pi_region_nth Ex ss ms i r HS); rewrite Hm; exact Hi).
pose proof (RN 2%nat r_eintr eq_refl) as G2. pose proof (RN 5%nat r_nout eq_refl) as G5.
pose proof (RN 6%nat r_capout eq_refl) as G6. pose proof (RN 7%nat r_out eq_refl) as G7.
pose proof (RN 8%nat r_broken eq_refl) as G8.
unfold r_eintr, r_nout, r_capout, r_out, r_broken in G2, G5, G6, G7, G8.
pose proof (HEI (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U11.
pose proof (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U12.
pose proof (HEI (A_HI 24) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U24.
pose proof (HEI (A_HI 25) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U25.
pose proof (HEI (A_HI 18) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U18.
split; [|split; [|split; [|split]]].
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 0 1%N (SOff 32 0) ei G2 U11 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HV11, Z.add_0_r in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 0 8%N (SOff 34 0) nov G5 U12 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HV12, Z.add_0_r in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 1976 8%N (SOff 35 0) capv G6 U24 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HH24 in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 2000 8%N (SOff 36 0) outv G7 U25 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HH25 in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 1212 1%N (SLit 0) 0 G8 U18 ltac:(cbn; left; reflexivity)
    ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HH18 in V. exact V.
Qed.
(* views and presence carried along the runs of a round: every frame_of / mem_grows from the start to the goal's memory *)
Ltac keep_chainW :=
  let a := fresh "a" in let Ha := fresh "Ha" in let HnW := fresh "HnW" in
  intros a Ha HnW;
  repeat match goal with
  | |- aview _ _ ?m a = aview _ _ ?m a => reflexivity
  | HF : frame_of _ _ (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- aview _ (w_H ?W) ?m2 a = _ =>
      rewrite (aview_kept_out _ _ (w_H W) m1 m2 HF a Ha HnW)
  end.
Ltac pres_chain :=
  let a := fresh "a" in let Hp := fresh "Hp" in
  intros a Hp;
  repeat match goal with
  | Hp' : apresent (w_H ?W) ?m a |- apresent (w_H ?W) ?m a => exact Hp'
  | Hp' : apresent (w_H ?W) ?m1 a, HG' : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
      apply (apresent_grows _ _ _ _ HG') in Hp'
  end.

(* len - sent as the engine computes it (0x829b4 sub s3,s0,s7): s0 + s7 * -1 *)
Lemma U_rem : forall E (len sent z : Z), ew E 8 = w64 len -> ew E 23 = w64 sent -> 0 <= sent <= len -> len < 2 ^ 64 ->
z mod 2 ^ 64 = 2 ^ 64 - 1 -> U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 23 0) (SLit z))) = len - sent.
Proof.
intros E len sent z E8 E23 Hs Hl Hz.
rewrite U_SAlu, U_SMd, (U_atom E 8 len E8), (U_atom E 23 sent E23), U_SLit by lia. cbn [zalu_raw zmd_raw].
unfold zcanon, M64. rewrite Hz, Z.add_mod_idemp_r by lia.
replace (len + sent * (2 ^ 64 - 1)) with ((len - sent) + sent * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* a data round: g_send_eintr = 0, g_send_dead = 0: n = sl_n mx (len - sent) at N (0x829cc, three ways of computing
   it made one by sl_canon), then the growth half (W_send_line_cx.v sl_grow_stmt) when g_out is short, else straight
   to the join J (0x82a08), and the copy half there (sl_copy_stmt) *)
Lemma sl_arm_data : sl_copy_stmt B MT MMAX RG -> sl_grow_stmt B MT MMAX RG -> forall n, sl_loop_at B MT MMAX RG n ->
forall regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL -> eiL = 0 -> ct_dd c = 0 ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat (Datatypes.S n) ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros COPY GROW n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hdd Hb.
(* ---- round prelude (begin) ---- *)
sl_intro HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & HstkL & _).
pose proof HstkL as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresL.
assert (WS : SL_STK = 16528) by reflexivity.
assert (HSF : SL_FRAME = 144) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev, Hclr, Hbrr, Hddr, Heir.
assert (Rcapout : 0 <= capL /\ 0 <= outL /\ no + sent <= 2 ^ 47 /\ capL <= 2 ^ 47 /\ outL <= 2 ^ 47).
{ destruct Hblk as [(Hz0 & Hz1 & Hz2) | (Hz3 & Hz4 & Hin1 & _)]; [repeat split; lia|].
  destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hin1) as (_ & Hp4 & Hpc & _).
  assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
  rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
assert (Hlen1 : 1 <= len <= 2 ^ 63 - 1) by lia.
assert (Hline4 : 4096 <= line).
{ destruct HLOK as [H0 | [(q & m & Hin & _ & Hq & _) | (Himg & _ & _)]]; [lia | |].
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL q m HARL Hin) as (_ & H4096 & _); lia.
  - pose proof (pa_img_range line (Himg line ltac:(lia))); lia. }
pose proof (sl_loop_entry lyL SL WL regsL memL (spZ regsE) len line sent eiL (ct_dd c)
  (no + sent) capL outL mx evL (O ++ firstn (Z.to_nat sent) Bl)
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR Hlen1 ltac:(lia) ltac:(lia)
  HSP HOUT ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
pose proof sl_bands as (Bcl & Bbr & Bei & Bdd & Bmx & Bno & Bcap & Bout & Berr).
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0 WS; lia).
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R23 & R24 & R25 & R27 & R21 & R26 & R22).
remember (Eimg (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsL 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact R9).
assert (E23 : ew E 23 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = w64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = w64 (ct_dd c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = w64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = w64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = w64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (NALL : VAL 252%nat = rg_send_eintr RG /\ VAL 253%nat = rg_nout RG /\ VAL 298%nat + 1212 = rg_client_broken RG /\
  VAL 300%nat + 1372 = rg_send_eintr RG /\ VAL 303%nat + 1372 = rg_nout RG /\ VAL 304%nat + 1976 = rg_capout RG /\
  VAL 305%nat + 2000 = rg_out RG)
  by (repeat split; first [exact HV11 | exact HV12 | exact HH18 | exact HH20 | exact HH23 | exact HH24 | exact HH25]).
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WL) memL)) by constructor.
assert (U9 : U E (SOff 9 0) = line) by (apply U_atom; [exact E9 | lia]).
assert (U23 : U E (SOff 23 0) = sent) by (apply U_atom; [exact E23 | lia]).
assert (UADD : U E (SAlu ALU_ADD (SOff 9 0) (SOff 23 0)) = line + sent)
  by (apply (trap_U_add E _ _ line sent U9 U23); lia).
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH1 FH1 GH1.
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite (trap_ptr_bltu E (SOff 9 0) (SAlu ALU_ADD (SOff 9 0) (SOff 23 0)) line (line + sent) U9 UADD
    ltac:(lia)) in Hc. discriminate Hc. }
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH2 FH2 GH2.
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite (trap_null_xor_folded E 24 E24) in Hc0. discriminate Hc0. }
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msH3 FH3 GH3.
(* ---- round prelude (end) ---- *)
psrr_branch_tok RUN BR HS SHOK LBspan.
2: { exfalso. rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc1 by (clear - Heir; lia).
  apply Z.eqb_neq in Hc1. lia. }
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msD FD0 GD0.
psrr_branch_tok RUN BR HS SHOK LBspan.
2: { exfalso. rewrite branch_eq_U, (U_atom E 33 (ct_dd c) E33), (U_lit E 0) in Hc2 by (clear - Hddr; lia).
  rewrite Hdd in Hc2. vm_compute in Hc2. discriminate Hc2. }
(* ---- the data round from 0x829ac: n at N, then the growth half or the join ---- *)
set (rem := len - sent) in *.
set (nn := sl_n mx rem) in *.
assert (Hnn : 0 < nn <= rem) by (apply sl_n_range; clear - Hmxr Hsent; lia).
pose (NF := mkAF 1 (2 ^ 63 - 1) 0).
pose (ssN := add_atom (mkSS A_sl_n
  (sr_set (sr_set (sr_set (sr_set sr_L 10%bv (SOff 37 0)) 18%bv (SAlu ALU_ADD (SOff 9 0) (SOff 23 0))) 19%bv (SOff 38 0))
     11%bv (SOff 39 0))
  l_regions None (mkFacts (f_atoms l_facts) [] [])) 38 NF).
assert (DATA : forall (ms0 : machine_state) (md0 : Model) (Ex : env),
  img_env VAL A_LIM Ex -> (forall m, (m < 38)%nat -> ew Ex m = ew E m) -> ew Ex 38 = w64 nn ->
  st_ok_pi SEGS VAL Ex ssN (restrict (w_H WL) ms0) ->
  ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S W mem md [] lyL SL WL (ms_mem ms0) md0 kL ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E l_regions a -> aview SEGS (w_H WL) (ms_mem ms0) a = aview SEGS (w_H WL) memL a) ->
  (forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem ms0) a) ->
  SRr SEGS WL (mkCfg ms0 md0) (sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl)).
{ intros ms0 md0 Ex HEIx OLDx X38 HSx HJx KEEP0 PR0.
  assert (BVEx : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ex (Some m) = VAL m)
    by (intros m Hm; cbn [base_val]; exact (HEIx m Hm)).
  assert (SHOKx : sh_ok SEGS BxL [] Ex (mrestrict (w_H WL) (ms_mem ms0))) by constructor.
  assert (F32 : ew Ex 32 = w64 0) by (rewrite OLDx by lia; rewrite E32, Hei0; reflexivity).
  assert (F34 : ew Ex 34 = w64 (no + sent)) by (rewrite OLDx by lia; exact E34).
  assert (F35 : ew Ex 35 = w64 capL) by (rewrite OLDx by lia; exact E35).
  assert (F36 : ew Ex 36 = w64 outL) by (rewrite OLDx by lia; exact E36).
  assert (F9 : ew Ex 9 = w64 line) by (rewrite OLDx by lia; exact E9).
  assert (F23 : ew Ex 23 = w64 sent) by (rewrite OLDx by lia; exact E23).
  rewrite Hdd, Hei0 in HOUT.
  assert (Hev0 : evL = (if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c))
    by (rewrite Hev, Hei0; destruct (ct_ei c =? 1); reflexivity).
  assert (R18x : forall ms1 ss1, st_ok_pi SEGS VAL Ex ss1 (restrict (w_H WL) ms1) ->
    nth 18 (ss_regs ss1) (SLit 0) = SAlu ALU_ADD (SOff 9 0) (SOff 23 0) ->
    getr (ms_regs ms1) 18%bv = w64 (line + sent)).
  { intros ms1 ss1 HS1 Hn. pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS1) as Hr.
    cbn [ms_regs restrict] in Hr. rewrite Hr.
    replace (nth (Z.to_nat (bv_unsigned (18%bv : bv 5))) (ss_regs ss1) (SLit 0)) with (SAlu ALU_ADD (SOff 9 0) (SOff 23 0))
      by (rewrite <- Hn; reflexivity).
    rewrite denot_lit_U. f_equal.
    apply (trap_U_add Ex _ _ line sent); [apply U_atom; [exact F9 | lia] | apply U_atom; [exact F23 | lia] | lia]. }
  destruct (Z.lt_ge_cases capL (no + sent + nn)) as [HGW | HNG].
  { (* g_out is short: the growth half (W_send_line_cx.v sl_grow_stmt), from N *)
    pose proof (l_vals Ex _ _ 0 (no + sent) capL outL HSx ltac:(vm_compute; reflexivity) HEIx F32 F34 F35 F36
      ltac:(lia) ltac:(clear - Rn47 HlenO; lia) ltac:(clear - Rc0 Rc47; lia) ltac:(clear - Ro0 Ro47; lia))
      as (NV1 & NV2 & NV3 & NV4 & NV5).
    cbn [ms_mem restrict] in NV1, NV2, NV3, NV4, NV5.
    assert (VIEW0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H WL) (ms_mem ms0) a = aview SEGS (w_H WL) memL a).
    { intros a Ha. destruct (l_cells_dec a) as [Hcl' | Hcl'].
      - rewrite Hei0 in Vei.
        destruct Hcl' as [Hx | [Hx | [Hx | [Hx | Hx]]]].
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 1 0 Vei NV1 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 8 _ Vno NV2 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 8 _ Vcap NV3 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 8 _ Vout NV4 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 1 0 Vbr NV5 a ltac:(cbn; lia)).
      - apply KEEP0; [exact Ha|]. intros Hw. exact (Hcl' (l_wrange_cells E a HEI Hw)). }
    destruct (sl_moved WL memL (ms_mem ms0) (aview_all_of_bounded _ _ _ VIEW0) PR0) as (MvO & MvG & MvR & MvV).
    pose proof (R18x ms0 ssN HSx eq_refl) as K18.
    prreg HSx (2%bv : bv 5) K2. prreg HSx (3%bv : bv 5) K3. prreg HSx (4%bv : bv 5) K4.
    prreg HSx (8%bv : bv 5) K8. prreg HSx (9%bv : bv 5) K9. prreg HSx (19%bv : bv 5) K19. prreg HSx (23%bv : bv 5) K23.
    prreg HSx (24%bv : bv 5) K24. prreg HSx (25%bv : bv 5) K25. prreg HSx (27%bv : bv 5) K27. prreg HSx (21%bv : bv 5) K21.
    prreg HSx (26%bv : bv 5) K26. prreg HSx (22%bv : bv 5) K22.
    pmkst HSx.
    apply (GROW regsE ly S W mem md c O mx no cap out line Bl WL (ms_regs ms0) (ms_mem ms0) md0 sent nn).
    2: { intros WM regsM memM mdM HM.
         apply (COPY n regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent nn IH HM).
         change (Z.of_nat (length Bl)) with len; clear - Hb Hei0; lia. }
    unfold SLN. cbv zeta. change (Z.of_nat (length Bl)) with len.
    exists lyL, SL, kL, evL, capL, outL, spent, rest.
    split; [exact HJx|].
    split; [unfold spZ at 1; rewrite K2, (OLDx 2%nat ltac:(lia)), E2; exact Hsp|].
    split; [rewrite K3, (OLDx 3%nat ltac:(lia)), E3; exact H3|].
    split; [rewrite K4, (OLDx 4%nat ltac:(lia)), E4; exact H4|].
    split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|].
    split.
    { unfold sl_regsM.
      rewrite K8, K9, K18, K19, K23, K24, K25, K27, K21, K26, K22.
      rewrite ?(OLDx 8%nat ltac:(lia)), ?(OLDx 9%nat ltac:(lia)), ?(OLDx 23%nat ltac:(lia)), ?(OLDx 24%nat ltac:(lia)),
        ?(OLDx 25%nat ltac:(lia)), X38.
      rewrite E8, E9, E23, E24, E25.
      rewrite !(ew_img _ _ HEIx) by (cbv; lia).
      repeat split; reflexivity. }
    split; [destruct HSP as (M0 & M8 & M16 & M24 & M32);
      split; [exact (MvV _ _ _ M0)|]; split; [exact (MvV _ _ _ M8)|]; split; [exact (MvV _ _ _ M16)|];
      split; [exact (MvV _ _ _ M24)|]; exact (MvV _ _ _ M32)|].
    split; [intros i Hi; exact (MvV _ _ _ (HSV i Hi))|].
    split; [exact Hcl|]. split; [exact Hbr|]. split; [exact Hdd|]. split; [exact Hsent|].
    split; [reflexivity|]. split; [exact Hev0|].
    split; [exact (MvO _ _ _ _ _ _ _ _ HOUT)|].
    split; [exact HGW|].
    split; [exact (MvG _ _ HGL)|]. split; [exact Hline0|]. split; [exact Hline1|].
    split; [exact (MvR HROM)|]. split; [exact HLOK|]. split; [exact HLG|].
    split; [exact (Hcapq Hdd)|]. split; [exact (HMM Hdd)|]. split; [exact (HLM Hdd)|].
    split; [intros a Ha1 Ha2 Ha3 Hp; exact (PR0 a (HAPK a Ha1 Ha2 Ha3 Hp))|].
    split; [exact HMOK|]. split; [exact HMLE|].
    split; [exact (HCOST Hdd)|].
    split; [exact HPerm0|]. split; [exact HPerm1|]. exact HFR. }
  (* g_capout >= g_nout + n: 0x829cc .. 0x829dc, the bgeu to the join *)
  lrun RUN HSx HJx SHOKx LBspan. { l_awr. } rn msJ0 FJ0 GJ0.
  (* the engine's g_nout + n: add s4,s3,s4 with s3 = n (atom 38), s4 = g_nout (atom 34) *)
  assert (UADDN : U Ex (SAlu ALU_ADD (SOff 34 0) (SOff 38 0)) = no + sent + nn).
  { rewrite U_SAlu, (U_atom Ex 38 nn X38), (U_atom Ex 34 (no + sent) F34) by (clear - Rn47 HlenO Hnn Hsent Hlen1; lia).
    cbn [zalu_raw]. rewrite zcanon_id; [lia|]. unfold M64. clear - Rn47 HlenO Hnn Hsent Hlen1; lia. }
  psrr_branch_tok RUN BR HSx SHOKx LBspan.
  2: { exfalso.
    lazymatch goal with Hg : branch_taken BC_GEU _ _ = false |- _ =>
      rewrite branch_geu_U, (U_atom Ex 35 capL F35), UADDN in Hg by (clear - Rc0 Rc47; lia);
      apply negb_false_iff, Z.ltb_lt in Hg; clear - Hg HNG; lia end. }
  lazymatch goal with Hg : branch_taken BC_GEU _ _ = true |- _ =>
    rewrite branch_geu_U, (U_atom Ex 35 capL F35), UADDN in Hg by (clear - Rc0 Rc47; lia);
    apply negb_true_iff, Z.ltb_ge in Hg; rename Hg into HGE end.
  lrun_to RUNTO HSx HJx SHOKx LBspan A_sl_join. { l_awr. } rn msJ FJ1 GJ1.
  pose proof (R18x msJ _ HSx ltac:(vm_compute; reflexivity)) as J18.
  pmkst HSx.
  apply (COPY n regsE ly S W mem md c O mx no cap out line Bl WL (ms_regs msJ) (ms_mem msJ) _ sent nn IH).
  2: (change (Z.of_nat (length Bl)) with len; clear - Hb Hei0; lia).
  prreg HSx (2%bv : bv 5) J2. prreg HSx (3%bv : bv 5) J3. prreg HSx (4%bv : bv 5) J4.
  prreg HSx (8%bv : bv 5) J8. prreg HSx (9%bv : bv 5) J9. prreg HSx (19%bv : bv 5) J19. prreg HSx (23%bv : bv 5) J23.
  prreg HSx (24%bv : bv 5) J24. prreg HSx (25%bv : bv 5) J25. prreg HSx (27%bv : bv 5) J27. prreg HSx (21%bv : bv 5) J21.
  prreg HSx (26%bv : bv 5) J26. prreg HSx (22%bv : bv 5) J22.
  pose proof (l_vals Ex _ _ 0 (no + sent) capL outL HSx ltac:(vm_compute; reflexivity) HEIx F32 F34 F35 F36
    ltac:(lia) ltac:(clear - Rn47 HlenO; lia) ltac:(clear - Rc0 Rc47; lia) ltac:(clear - Ro0 Ro47; lia))
    as (JV1 & JV2 & JV3 & JV4 & JV5).
  cbn [ms_mem restrict] in JV1, JV2, JV3, JV4, JV5.
  assert (VIEW : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H WL) (ms_mem msJ) a = aview SEGS (w_H WL) memL a).
  { intros a Ha. destruct (l_cells_dec a) as [Hcl' | Hcl'].
    - rewrite Hei0 in Vei.
      destruct Hcl' as [Hx | [Hx | [Hx | [Hx | Hx]]]].
      + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 1 0 Vei JV1 a ltac:(cbn; lia)).
      + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 8 _ Vno JV2 a ltac:(cbn; lia)).
      + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 8 _ Vcap JV3 a ltac:(cbn; lia)).
      + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 8 _ Vout JV4 a ltac:(cbn; lia)).
      + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 1 0 Vbr JV5 a ltac:(cbn; lia)).
    - assert (HnW : ~ in_wrange E l_regions a) by (intros Hw; exact (Hcl' (l_wrange_cells E a HEI Hw))).
      assert (HnWx : ~ in_wrange Ex l_regions a) by (intros Hw; exact (Hcl' (l_wrange_cells Ex a HEIx Hw))).
      rewrite <- (KEEP0 a Ha HnW).
      rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msJ) FJ1 a Ha HnWx).
      rewrite (aview_kept_out _ _ (w_H WL) _ (ms_mem msJ0) FJ0 a Ha HnWx).
      reflexivity. }
  assert (PRJ : forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem msJ) a)
    by (intros a Hp; apply (apresent_grows _ _ _ _ GJ1); apply (apresent_grows _ _ _ _ GJ0); exact (PR0 a Hp)).
  destruct (sl_moved WL memL (ms_mem msJ) (aview_all_of_bounded _ _ _ VIEW) PRJ) as (MvO & MvG & MvR & MvV).
  assert (NOG : (capL <? no + sent + nn) = false) by (apply Z.ltb_ge; exact HGE).
  unfold SLM. cbv zeta. change (Z.of_nat (length Bl)) with len.
  exists lyL, SL, kL, evL, capL, outL, spent, rest.
  split; [exact HJx|].
  split; [unfold spZ at 1; rewrite J2, (OLDx 2%nat ltac:(lia)), E2; exact Hsp|].
  split; [rewrite J3, (OLDx 3%nat ltac:(lia)), E3; exact H3|].
  split; [rewrite J4, (OLDx 4%nat ltac:(lia)), E4; exact H4|].
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|].
  split.
  { unfold sl_regsM.
    rewrite J8, J9, J18, J19, J23, J24, J25, J27, J21, J26, J22.
    rewrite ?(OLDx 8%nat ltac:(lia)), ?(OLDx 9%nat ltac:(lia)), ?(OLDx 23%nat ltac:(lia)), ?(OLDx 24%nat ltac:(lia)),
      ?(OLDx 25%nat ltac:(lia)), X38.
    rewrite E8, E9, E23, E24, E25.
    rewrite !(ew_img _ _ HEIx) by (cbv; lia).
    repeat split; reflexivity. }
  split; [destruct HSP as (M0 & M8 & M16 & M24 & M32);
    split; [exact (MvV _ _ _ M0)|]; split; [exact (MvV _ _ _ M8)|]; split; [exact (MvV _ _ _ M16)|];
    split; [exact (MvV _ _ _ M24)|]; exact (MvV _ _ _ M32)|].
  split; [intros i Hi; exact (MvV _ _ _ (HSV i Hi))|].
  split; [exact Hcl|]. split; [exact Hbr|]. split; [exact Hdd|]. split; [exact Hsent|].
  split; [reflexivity|]. split; [exact Hev0|].
  split; [exact (MvO _ _ _ _ _ _ _ _ HOUT)|].
  split; [exact HGE|].
  split; [exact (MvG _ _ HGL)|]. split; [exact Hline0|]. split; [exact Hline1|].
  split; [exact (MvR HROM)|]. split; [exact HLOK|]. split; [exact HLG|].
  split.
  { rewrite (Hcapq Hdd), send_line_cap_step by (clear - Hmxr Hsent; lia). fold rem nn.
    unfold sl_capn. rewrite NOG. reflexivity. }
  split.
  { pose proof (HMM Hdd) as HM. rewrite sl_max_run_step in HM by (clear - Hmxr Hsent; lia). fold rem nn in HM.
    rewrite NOG in HM. exact HM. }
  split.
    { pose proof (HLM Hdd) as HM.
      rewrite (sl_tr_peak_keep mx (no + sent) capL rem ltac:(clear - Hmxr; lia) ltac:(clear - Hsent; lia) HGE) in HM.
      exact HM. }
  split; [intros a Ha1 Ha2 Ha3 Hp; exact (PRJ a (HAPK a Ha1 Ha2 Ha3 Hp))|].
  split; [exact HMOK|]. split; [exact HMLE|].
  split.
  { pose proof (HCOST Hdd) as HM. rewrite sl_cost_run_step in HM by (clear - Hmxr Hsent; lia). fold rem nn in HM.
    unfold sl_capn in HM. rewrite NOG in HM. cbv beta iota in HM. fold rem nn. clear - HM. lia. }
  split; [exact HPerm0|]. split; [exact HPerm1|]. exact HFR. }
(* 0x829ac .. 0x829bc: mx = g_send_max, s3 = len - sent, bltu s3, mx *)
lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msK1 FK1 GK1.
assert (Urem1 : U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 23 0) (SLit (-1)))) = rem)
  by (apply U_rem; first [exact E8 | exact E23 | clear - Hsent Hlen1; lia | reflexivity]).
psrr_branch_tok RUN BR HS SHOK LBspan.
- (* rem < mx: n = rem *)
  rewrite branch_ltu_U, Urem1, (U_atom E 37 mx E37) in Hc3 by (clear - Hmxr; lia).
  lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msK2 FK2 GK2.
  psrr_branch_tok RUN BR HS SHOK LBspan.
  + exfalso. rewrite branch_eq_U, (U_atom E 37 mx E37), (U_lit E 0) in Hc4 by (clear - Hmxr; lia).
    apply Z.eqb_eq in Hc4. apply Z.ltb_lt in Hc3. clear - Hc3 Hc4 Hnn. lia.
  + lrun_to RUNTO HS HJ SHOK LBspan A_sl_n. { l_awr. } rn msK FK3 GK3.
    assert (V19 : getr (ms_regs msK) 19%bv = w64 nn).
    { rewrite (st_ok_pi_restrict_reg _ _ _ _ 19%bv HS).
      lazymatch goal with |- sv_denot E ?e = _ => let e' := eval vm_compute in e in change e with e' end.
      rewrite denot_lit_U, (U_rem E len sent _ E8 E23) by (first [clear - Hsent Hlen1; lia | reflexivity]).
      unfold nn, sl_n. apply Z.ltb_lt in Hc3. rewrite (proj2 (Z.eqb_neq mx 0)) by (clear - Hc3 Hnn; lia).
      rewrite (proj2 (Z.ltb_ge mx rem)) by (clear - Hc3; lia). reflexivity. }
    assert (X38 : ew (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 = w64 nn) by (unfold havoc; cbn [ew]; reflexivity).
    assert (NFok : afact_ok (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 NF).
    { unfold afact_ok, NF. cbn [af_lo af_hi af_al2]. rewrite X38. unfold w64.
      rewrite unsigned_lit_small by (clear - Hnn Hlen1 Hsent; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Hnn Hlen1 Hsent; lia. }
    pose proof (sl_canon E _ _ (w64 nn) (getr (ms_regs msK) 11%bv) NF HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ms_regs restrict]; exact V19) ltac:(cbn [ms_regs restrict]; reflexivity) NFok) as HSn.
    lazymatch type of HSn with st_ok_pi ?a ?b ?c _ ?d => change (st_ok_pi a b c ssN d) in HSn end.
    eapply (DATA msK _ (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]));
      [ apply img_env_havoc; [exact HEI | cbv; lia]
      | intros m Hm; apply YN3v.ew_havoc_old; exact Hm
      | exact X38 | exact HSn | exact HJ | keep_chainW | pres_chain ].
- (* rem >= mx *)
  rewrite branch_ltu_U, Urem1, (U_atom E 37 mx E37) in Hc3 by (clear - Hmxr; lia).
  apply Z.ltb_ge in Hc3.
  lrun RUN HS HJ SHOK LBspan. { l_awr. } rn msK2 FK2 GK2.
  psrr_branch_tok RUN BR HS SHOK LBspan.
  + (* mx = 0: n = rem *)
    rewrite branch_eq_U, (U_atom E 37 mx E37), (U_lit E 0) in Hc4 by (clear - Hmxr; lia).
    assert (Hmx0 : (mx =? 0) = true) by exact Hc4.
    lrun_to RUNTO HS HJ SHOK LBspan A_sl_n. { l_awr. } rn msK FK3 GK3.
    assert (V19 : getr (ms_regs msK) 19%bv = w64 nn).
    { rewrite (st_ok_pi_restrict_reg _ _ _ _ 19%bv HS).
      lazymatch goal with |- sv_denot E ?e = _ => let e' := eval vm_compute in e in change e with e' end.
      rewrite denot_lit_U, (U_rem E len sent _ E8 E23) by (first [clear - Hsent Hlen1; lia | reflexivity]).
      unfold nn, sl_n. rewrite Hmx0. reflexivity. }
    assert (X38 : ew (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 = w64 nn) by (unfold havoc; cbn [ew]; reflexivity).
    assert (NFok : afact_ok (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 NF).
    { unfold afact_ok, NF. cbn [af_lo af_hi af_al2]. rewrite X38. unfold w64.
      rewrite unsigned_lit_small by (clear - Hnn Hlen1 Hsent; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Hnn Hlen1 Hsent; lia. }
    pose proof (sl_canon E _ _ (w64 nn) (getr (ms_regs msK) 11%bv) NF HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ms_regs restrict]; exact V19) ltac:(cbn [ms_regs restrict]; reflexivity) NFok) as HSn.
    lazymatch type of HSn with st_ok_pi ?a ?b ?c _ ?d => change (st_ok_pi a b c ssN d) in HSn end.
    eapply (DATA msK _ (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]));
      [ apply img_env_havoc; [exact HEI | cbv; lia]
      | intros m Hm; apply YN3v.ew_havoc_old; exact Hm
      | exact X38 | exact HSn | exact HJ | keep_chainW | pres_chain ].
  + (* mx <> 0 and mx <= rem: n = mx *)
    rewrite branch_eq_U, (U_atom E 37 mx E37), (U_lit E 0) in Hc4 by (clear - Hmxr; lia).
    apply Z.eqb_neq in Hc4. assert (Hmx0 : mx <> 0) by exact Hc4.
    lrun_to RUNTO HS HJ SHOK LBspan A_sl_n. { l_awr. } rn msK FK3 GK3.
    assert (V19 : getr (ms_regs msK) 19%bv = w64 nn).
    { rewrite (st_ok_pi_restrict_reg _ _ _ _ 19%bv HS).
      lazymatch goal with |- sv_denot E ?e = _ => let e' := eval vm_compute in e in change e with e' end.
      rewrite denot_lit_U, (U_atom E 37 mx E37) by (clear - Hmxr; lia).
      unfold nn, sl_n. rewrite (proj2 (Z.eqb_neq mx 0)) by exact Hmx0.
      destruct (Z.ltb_spec mx rem) as [Hlt|Hge]; cbn [negb andb]; [reflexivity | f_equal; clear - Hc3 Hge; lia]. }
    assert (X38 : ew (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 = w64 nn) by (unfold havoc; cbn [ew]; reflexivity).
    assert (NFok : afact_ok (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 NF).
    { unfold afact_ok, NF. cbn [af_lo af_hi af_al2]. rewrite X38. unfold w64.
      rewrite unsigned_lit_small by (clear - Hnn Hlen1 Hsent; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Hnn Hlen1 Hsent; lia. }
    pose proof (sl_canon E _ _ (w64 nn) (getr (ms_regs msK) 11%bv) NF HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ms_regs restrict]; exact V19) ltac:(cbn [ms_regs restrict]; reflexivity) NFok) as HSn.
    lazymatch type of HSn with st_ok_pi ?a ?b ?c _ ?d => change (st_ok_pi a b c ssN d) in HSn end.
    eapply (DATA msK _ (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]));
      [ apply img_env_havoc; [exact HEI | cbv; lia]
      | intros m Hm; apply YN3v.ew_havoc_old; exact Hm
      | exact X38 | exact HSn | exact HJ | keep_chainW | pres_chain ].
Qed.

(* The loop segment, given the copy half (sl_copy_stmt) and the growth half (sl_grow_stmt) of a data round: an
   induction on the bound n >= 2 (len - sent) + g_send_eintr; each round is one of the three arms. *)
Theorem pb_sl_loop_cut : sl_copy_stmt B MT MMAX RG -> sl_grow_stmt B MT MMAX RG -> sl_loop_stmt B MT MMAX RG.
Proof.
intros COPY GROW. unfold sl_loop_stmt. intros n. induction n as [|n IH];
intros regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hb;
pose proof HI as HI'; sl_intro HI';
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hddr & Heir & _);
cbn [ct_dd ct_ei] in Hddr, Heir.
- exfalso. lia.
- destruct (Z.eq_dec eiL 0) as [Hei0 | Hei0].
  + destruct Hddr as [Hd | Hd].
    * exact (sl_arm_data COPY GROW n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hd Hb).
    * exact (sl_arm_dead regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hd).
  + exact (sl_arm_eintr n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hb).
Qed.
End c.
End b.
End a.
