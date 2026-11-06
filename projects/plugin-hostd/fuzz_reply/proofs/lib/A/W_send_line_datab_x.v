(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ARx-generic twin of lib/A/W_send_line_datab.v's sl_copy (the copy half of a
   data round of fuzz_reply's ASan send_line loop), from W7's stopped conversion d12b637bb01; W_send_line_datab.v is
   NOT edited. *)
(* From the join A_sl_join = 0x82850 (W_send_line_datab_cx.v SLM) to the loop head or the epilogue:
     0x82850 ld a0,892(s4)  (g_out)          0x82854 ld s3,260(s10)  (g_nout = no + sent)
     0x82858 add a1,s1,s6   (line + sent)    0x8285c add a0,a0,s3    (g_out + no + sent)
     0x82860 mv a2,s2       (n)              0x82864 jal __asan_memcpy  (AMEMCPY)
     0x82868 add s3,s3,s2   0x8286c sd s3,260(s10)  (g_nout := no + sent + n)
     0x82870 bltz s2,0x82884   never taken: 0 < n < 2 ^ 30
     0x82874 li s3,3
     0x82878 beqz s2,0x828ec   never taken: 0 < n
     0x8287c add s6,s2,s6   (sent := sent + n)   0x82880 j 0x828a8
     0x828a8 bltu s6,s0,0x827c8   taken: sent + n < len, back to the loop head L (sl_loop_at n0)
     0x828ac j 0x828f8            not taken: sent + n = len, the epilogue (W_send_line_cx.v sl_epi)
   The memcpy's source check needs the line's bytes addressable and the shadow hull of the line visible (W_sites_x.v
   aintrin_realizes_x, OCpy).  A heap line has both (W_journal_x.v range_addressable_of_block_hp0_x,
   shadow_hull_vis_of_block_hp0_x); an image line has them over all of [line, line + len) by sl_line_ok_x's ashp_x
   (W_contract_x.v), and over the round's sub-range [line + sent, line + sent + n) by range_addressable_sub and
   sc_hull_sub.
   The walk is GENERIC (route (b), step 3): sl_copy_x, over any allocator relation ARx with its laws and any room record
   RP, is proved in Section c, whose Variables and Hypotheses are W_send_line_datab_cx_x.v's, verbatim.  W7's skeleton
   took two more Section hypotheses (W_kit_x.v's IMGC / BLKN, for blk_off_imgP_x and a live block's size); this file
   needs neither: g_out's block is off the image by the client-image law (every byte of a live block is outside
   in_img, and every cell the walk reads or writes is an image byte by HG / HGO), and the one block whose uniqueness
   the destination's awr needs has a positive size (sc_blk_once_x, from the separation law).  The room conjuncts
   (rp_RM, cnt_ok_pk) are carried: the copy half calls no allocator. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_frame W_sites W_contract W_send_line_cx W_send_line_datab_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_send_line_cx_x W_send_line_datab_cx_x.
(* route R: the send_line contract texts at a world relation R (a Theorem Labs lane's W_send_line_xR.v) and SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_send_line_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma sc_n_range : forall mx rem, 0 <= mx -> 0 < rem -> 0 < sl_n mx rem <= rem.
Proof.
intros mx rem Hmx Hrem. unfold sl_n.
destruct (Z.eqb_spec mx 0); destruct (Z.ltb_spec mx rem); simpl; lia.
Qed.
Lemma sc_zall_nth : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
Lemma sc_zpw_nth : forall l i j d, zpairwise_disjoint l -> i <> j ->
(i < length l)%nat -> (j < length l)%nat -> zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hi Hj; cbn in Hi, Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i], j as [|j]; cbn [nth]; [lia | | |].
- apply sc_zall_nth; [exact H1 | lia].
- pose proof (sc_zall_nth a l i d H1 ltac:(lia)) as D. unfold zdisj in *. lia.
- apply IH; [exact H2 | lia | lia | lia].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* ---- THE GENERIC WALK: the copy half over any allocator relation ARx with its laws and any room record RP, stated as
   W_send_line_datab_cx_x.v's sl_copy_stmt_x.  The Section's Variables and Hypotheses are that file's, verbatim. ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* a Theorem Labs lane's HP0 ruling: the generic relation holds at the empty ghost list only *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* a live block's request is below 2 ^ 30 (W_LLVMFuzzerTestOneInput_exit_x.v:236 BLKM's text; the top states it at ARX,
   top_x.v:972, from the cf instance's AR_blocks_law_cf): the memcpy at 0x82864 needs n < 2 ^ 32 (a Theorem Labs lane) *)
Hypothesis BLKM : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 30.
(* W_send_line_cx_x.v's header (W_send_line_datab_cx.v's is W_send_line_cx.v's) *)
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
(* The realloc site rule in its caller-context form (W_journal_x.v Section hc), as the top's ARE_x states it
   (CTX_AREALLOC, ACk0.v:45, holds [0x82844]); send_line hands the rule a cut chain (ch = []), so the trace is the
   return address alone (W7's ccd62d4c6f6 form). *)
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_slr : In [BASE + AF_fr_send_line + 0x110] CTX_R.   (* realloc returns to 0x82844 *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
(* errno's 4 bytes in an 8-aligned zero-shadow range (W_contract.azs; W_drain_cx_x.v:189's form): the loop's errno
   stores need range_addressable of errno at an ARx state (W_contract_x.azs_range_addressable_x) *)
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
Let RUN := paj_run_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Definition JBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* The shadow hull of a sub-range lies inside the range's hull (shadow_addr is monotone; YG0d.v:319). *)
Lemma sc_hull_sub : forall (rd : Z -> option Z) x n x' n',
shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H Hx Hn Hn' s Hs. apply H.
assert (M1 : shadow_addr x / 8 * 8 <= shadow_addr x' / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr.
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (M2 : shadow_addr (x' + n' - 1) / 8 * 8 <= shadow_addr (x + n - 1) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr.
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

(* HRGD as the zdisj fact of two of its extents, named by their positions in the list:
   0 VAL (A_OBJ 0), 1 VAL (A_OBJ 32), 2 g_client, 3 g_client_broken, 4 g_send_eintr, 5 g_send_dead,
   6 g_send_max, 7 g_nout, 8 g_capout, 9 g_out, 10 errno *)
Lemma sc_rgd : forall i j, i <> j -> (i < 11)%nat -> (j < 11)%nat ->
zdisj (nth i [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)] (0, 0))
(nth j [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)] (0, 0)).
Proof. intros i j Hij Hi Hj. apply sc_zpw_nth; [exact HRGD | exact Hij | cbn; lia | cbn; lia]. Qed.

(* membership in the walk's globals *)
Ltac ing_tac := unfold G_SL; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
Ltac clia := repeat match goal with X : _ |- _ => clear X end; lia.
Ltac awr_empty :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; intros a Ha; exfalso; clear - Ha; lia.
Ltac awr_gb BV m H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
  rewrite (BV m) by (repeat match goal with X : _ |- _ => clear X end; unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia);
  intros a Ha; clear - Ha H; ing_tac.

(* W_kit_x.v's paj_run_tok_x / paj_run_to_tok_x (the generic chain: 16 holes) with a fuel that fits one round
   (W_send_line_loop.v lrun). *)
Definition J_FUEL : N := 3000%N.
Ltac jrun RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH J_FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH J_FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "jrun: no img_env" end in
eapply (RUN W J_FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
end.
Ltac jrun_to RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH J_FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH J_FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "jrun_to: no img_env" end in
eapply (RUNTO W J_FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
end.

(* ---- The join's symbolic state. ----
   Atoms: the 32 registers (s0 = len, s1 = line, s2 = n, s6 = sent, s7 = the shadow base), 32 = g_nout = no + sent,
   33 = g_out = outM.  The six kept auipc registers are the listing's hi atoms (a PLdHi slot runs only when its base
   register holds SOff (A_HI j) 0).  The two cells are read through their object atoms (PLdHi at 0x82850 / 0x82854);
   g_nout is rebased onto s10 = A_HI 22 before the store at 0x8286c. *)
Definition sr_J : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    20%bv (SOff (A_HI 24) 0))
    21%bv (SOff (A_HI 16) 0))
    24%bv (SOff (A_HI 23) 0))
    25%bv (SOff (A_HI 19) 0))
    26%bv (SOff (A_HI 22) 0))
    27%bv (SOff (A_HI 20) 0).
Definition j_nout : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition j_out : YP09.region := YP09.mkRegion (Some (A_OBJ 15)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition j_regions : smem := [ j_nout; j_out ].
Definition JOBJF : afact := mkAF 0x10000 0x5fb000 0.
Definition JHIF : afact := mkAF 0 0x5fb000 0.
Definition j_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (23%nat, mkAF SB SB 0);
  (8%nat, mkAF 1 (2^63 - 1) 0); (9%nat, mkAF 0 (2^63 - 1) 0); (22%nat, mkAF 0 (2^63 - 1) 0);
  (18%nat, mkAF 1 (2^30) 0); (32%nat, mkAF 0 (2^47) 0); (33%nat, mkAF 0 (2^47) 0);
  (A_OBJ 13, JOBJF); (A_OBJ 15, JOBJF); (A_HI 22, JHIF); (A_HI 24, JHIF) ] [] [].
Definition ss_J : sstate := mkSS A_sl_join sr_J j_regions None j_facts.
Definition BxJ : sv := SOff 23 0.
Definition j_extra (no' outM : Z) : list word := map (Z_to_bv 64) [no'; outM].

Lemma sl_join_entry : forall (WM : world SEGS) regsM memM sp0 len line sent n no' outM,
spZ regsM = sp0 - SL_FRAME ->
2 ^ 46 + SL_FRAME <= sp0 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
sl_regsM regsM len line sent n ->
1 <= len <= 2 ^ 63 - 1 -> 0 <= line <= 2 ^ 63 - 1 -> 0 <= sent <= 2 ^ 63 - 1 -> 1 <= n <= 2 ^ 30 ->
val_mem SEGS (arm WM memM) (rg_nout RG) 8 no' -> awr WM memM (rg_nout RG) 8 ->
val_mem SEGS (arm WM memM) (rg_out RG) 8 outM ->
0 <= no' <= 2 ^ 47 -> 0 <= outM <= 2 ^ 47 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsM (j_extra no' outM))) ss_J
(restrict (w_H WM) (mkst regsM (Z_to_bv 64 (BASE + A_sl_join)) memM (seg_rom SEGS))).
Proof.
intros WM regsM memM sp0 len line sent n no' outM Hsp Hlo Hhi Hal HR Hlen Hline Hsent Hn Vno Wno Vout Rno Rout.
unfold SL_FRAME in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HR as (R8 & R9 & R18 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsM (j_extra no' outM))).
assert (E2 : ew E 2 = getr regsM 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regsM 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regsM 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = getr regsM 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 18 18%bv eq_refl)).
assert (E22 : ew E 22 = getr regsM 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr regsM 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 no') by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 outM) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 1)).
assert (UV : forall k, (A_TEXT <= k < A_LIM)%nat -> bv_unsigned (ew E k) = VAL k).
{ intros k Hk. subst E. rewrite Eimg_img by exact Hk. apply unsigned_lit_small. apply pa_val_range. }
assert (BV : forall k, (A_TEXT <= k < A_LIM)%nat -> base_val E (Some k) = VAL k).
{ intros k Hk. cbn [base_val]. exact (UV k Hk). }
assert (SVH : forall k, (A_TEXT <= k < A_LIM)%nat -> sv_denot E (SOff k 0) = w64 (VAL k)).
{ intros k Hk. cbn [sv_denot]. rewrite (UV k Hk). rewrite Z.add_0_r. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite E2; exact Hsp).
pose proof (pa_obj_img 13 ltac:(lia)) as Q13. pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
unfold ss_J, A_sl_join, A_sl_loop. apply pa_entry_st_ok_full.
- unfold sr_J.
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 20)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R27].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 22)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R26].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 19)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R25].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 23)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R24].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 16)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R21].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 24)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R20].
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold j_regions, j_nout, j_out.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (BV (A_OBJ 13)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wno; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_nout RG) 0 8 (SOff 32 0) no');
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vno.
  + rewrite (BV (A_OBJ 15)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV15.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_out RG) 0 8 (SOff 33 0) outM);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vout.
- apply pairwise_disjoint_of_extents.
  unfold j_regions, j_nout, j_out, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (BV (A_OBJ 13)), (BV (A_OBJ 15)) by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite HV13, HV15.
  pose proof (sc_rgd 7 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D. cbn [nth] in D. unfold zdisj in D. cbn [fst snd] in D.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [j_facts f_atoms atoms_ok]. unfold afact_ok, JOBJF, JHIF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E8, E9, E18, E22, E23, E32, E33.
  rewrite R8, R9, R18, R22, R23.
  rewrite (UV (A_OBJ 13)), (UV (A_OBJ 15)), (UV (A_HI 22)), (UV (A_HI 24))
    by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I;
  first [ rewrite Zminus_mod, Hal; reflexivity
        | solve [ clear - Hlo Hhi Hlen Hline Hsent Hn Rno Rout Q13 Q15 HH22 HH24 HV13 HV15; unfold SB; lia ] ].
Qed.

(* the sum of two atoms, as the engine forms an address *)
Lemma sc_add_atoms : forall E i j a b, ew E i = w64 a -> ew E j = w64 b -> 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff i 0) (SOff j 0)) = w64 (a + b).
Proof.
intros E i j a b Hi Hj Ha Hb Hab. rewrite denot_lit_U, U_SAlu, (U_atom E i a Hi), (U_atom E j b Hj) by lia.
cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

(* A live block of positive request size occurs once in the block list: the separation law makes the extents of
   two copies of it disjoint, which a non-empty extent is not (in place of W_drain_linea.v la_ablocks_nodup, whose
   proof needs every live block's size non-negative: W_kit_x.v's BLKN, which ARx's laws do not give). *)
Definition sc_zz_eq : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma sc_pw_once : forall (L : list (Z * Z)) x,
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) L) -> 1 <= req_size (snd x) ->
(count_occ sc_zz_eq L x <= 1)%nat.
Proof.
intros L x. induction L as [|b L IH]; intros Hpw Hx; [cbn; lia|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw].
cbn [count_occ]. destruct (sc_zz_eq b x) as [<- | Hne].
- assert (Hn : ~ In b L).
  { intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
    unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia. }
  rewrite (proj1 (@count_occ_not_In (Z * Z) sc_zz_eq L b) Hn). lia.
- exact (IH Hpw Hx).
Qed.
Lemma sc_blk_once_x : forall ly S Hp W mem md x l, ARx ly S Hp W mem md ->
Permutation (ablocks B ly S) (x :: l) -> 1 <= req_size (snd x) -> ~ In x l.
Proof.
intros ly S Hp W mem md x l HAR HQ Hx Hin.
destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [Hq _].
pose proof (sc_pw_once _ x Hq Hx) as C.
rewrite (proj1 (@Permutation_count_occ (Z * Z) sc_zz_eq _ _) HQ x) in C.
pose proof (proj1 (@count_occ_In (Z * Z) sc_zz_eq l x) Hin) as P.
revert C. cbn [count_occ]. destruct (sc_zz_eq x x) as [_ | Hne]; [intros C; lia | intros _; exact (Hne eq_refl)].
Qed.

(* A byte of g_out's block is the journal's to write: the block is the caller's (out, cap), in its footprint, or a
   block the walk allocated (the growth round's realloc). *)
Lemma sc_dest_awr_x : forall ly S lyM SM HpM (WM : world SEGS) memM mdM cap out capM outM rest STK sp0 a,
ARx lyM SM HpM WM memM mdM ->
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) ->
Permutation (ablocks B lyM SM) (aout_blks capM outM ++ rest) ->
0 < capM -> outM <= a < outM + capM ->
awr_byte STK sp0 (ablocks_fp (aout_blks cap out)) (ablocks B ly S) (ablocks B lyM SM) lyM [] a.
Proof.
intros ly S lyM SM HpM WM memM mdM cap out capM outM rest STK sp0 a HAR HQ0 HQ1 Hc Ha.
assert (Eb : aout_blks capM outM = [(outM, capM)])
  by (unfold aout_blks; rewrite (proj2 (Z.eqb_neq capM 0)) by lia; reflexivity).
rewrite Eb in HQ1. cbn [app] in HQ1.
assert (HinM : In (outM, capM) (ablocks B lyM SM)) by (apply (Permutation_in _ (Permutation_sym HQ1)); left; reflexivity).
assert (Hrq : req_size capM = capM) by (unfold req_size; destruct (Z.eqb_spec capM 0); lia).
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (outM, capM) (ablocks B ly S)) as [H0 | H0].
- right. left. split.
  + pose proof (Permutation_in _ HQ0 H0) as H1. apply in_app_or in H1 as [H1 | H1].
    * unfold aout_blks in H1. destruct (cap =? 0) eqn:Hc0; [destruct H1|]. destruct H1 as [Heq | []].
      injection Heq as Ho Hcc. subst out cap.
      replace a with (outM + (a - outM)) by lia. apply (inFP_ablocks_fp _ outM capM).
      -- unfold aout_blks. rewrite Hc0. left. reflexivity.
      -- rewrite Hrq. lia.
    * exfalso. apply (sc_blk_once_x _ _ _ _ _ _ (outM, capM) rest HAR HQ1); [cbn [snd]; rewrite Hrq; lia | exact H1].
  + exists outM, capM. split; [exact HinM | rewrite Hrq; lia].
- right. right. left. exists outM, capM. split; [exact HinM|]. split; [exact H0 | rewrite Hrq; lia].
Qed.

(* prreg without the normalisation: the register's symbolic value as it is *)
Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

(* a byte outside g_nout is outside every write window of the copy half's states (the only window is g_nout) *)
Ltac sc_nowr_n BV Hnn N1 N2 :=
  let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (rr & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      first [ solve [ clear - Hr; lia ]
            | solve [ exfalso; rewrite ?(BV 254%nat ltac:(cbv; lia)), ?(BV 302%nat ltac:(cbv; lia)) in Hr;
                      apply Hnn; clear - Hr N1 N2; lia ] ] | ]);
  try destruct Hin.

Lemma sc_mbyte_of_aview2 : forall H (m m' : word -> option byte) x y,
aview SEGS H m' x = aview SEGS H m y -> mbyte SEGS (mrestrict H m') x = mbyte SEGS (mrestrict H m) y.
Proof.
intros H m m' x y E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m') x) as [b'|], (mbyte SEGS (mrestrict H m) y) as [b|]; cbn in E;
  try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* bytes copied from a garr8 run of one memory to another place of another memory *)
Lemma sc_garr8_copy : forall (W : world SEGS) m m' a a' (l : list Z) k len,
garr8 SEGS (arm W m) a l -> (k + len <= length l)%nat ->
(forall j, 0 <= j < Z.of_nat len -> aview SEGS (w_H W) m' (a' + j) = aview SEGS (w_H W) m (a + Z.of_nat k + j)) ->
garr8 SEGS (arm W m') a' (firstn len (skipn k l)).
Proof.
intros W m m' a a' l k len Hg Hk Hv j Hj.
rewrite length_firstn, length_skipn in Hj.
assert (Hj' : (k + j < length l)%nat) by lia.
rewrite nth_firstn, nth_skipn. replace (j <? len)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
destruct (Hg (k + j)%nat Hj') as [Hv0 Hr]. split; [|exact Hr].
intros k0 Hk0. assert (k0 = 0%nat) by lia. subst k0. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (Hv0 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
unfold arm in *. rewrite (sc_mbyte_of_aview2 (w_H W) m m' (a' + Z.of_nat j) (a + Z.of_nat (k + j))).
- exact Hv0.
- rewrite (Hv (Z.of_nat j) ltac:(lia)). f_equal. lia.
Qed.
Lemma sc_firstn_add : forall {X : Type} (l : list X) a b, firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
intros X l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
destruct l as [|x l]; [cbn; rewrite firstn_nil; reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.
(* A value is carried by a memory that keeps the view of its bytes (W_send_line_loop.v vm_keep). *)
Lemma sc_vm_keep : forall (W : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v HK Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
apply HK. lia.
Qed.

(* errno's 4 bytes are image bytes (they are G_SL's) *)
Lemma sc_errno_img : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000.
Proof.
assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
{ intros i Hi. assert (Hin : inG (G_SL B RG) (as_errno B + i)) by (clear - Hi; ing_tac).
  exact (proj1 (HG _ Hin)). }
pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0.
pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3. clear - P0 P3. lia.
Qed.

(* membership in a literal list of ranges (HGO's) *)
Ltac ing_tac0 := repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
(* a cell byte is an image byte (HG / HGO), and g_out's block holds no image byte (HOB) *)
Local Ltac sc_cell_img x Hx :=
  first [ exact (proj1 (HG x ltac:(clear - Hx; solve [ing_tac])))
        | exact (proj1 (HGO x ltac:(clear - Hx; solve [ing_tac0]))) ].
(* a cell of aout_at (position i of HRGD, an image byte by HG / HGO) is kept by the copy half, which changes only
   g_nout (position 7) and bytes of g_out's block (which holds no image byte) *)
Local Ltac sc_kl HK i C HOB :=
  let x := fresh "x" in let Hx := fresh "Hx" in let D1 := fresh "D" in let Hd := fresh "Hd" in
  intros x Hx;
  pose proof (sc_rgd i 7 ltac:(lia) ltac:(lia) ltac:(lia)) as D1;
  cbn [nth] in D1; unfold zdisj in D1; cbn [fst snd] in D1;
  apply HK; [ pose proof asan_consts as (CC1 & _); clear - Hx C CC1; lia | clear - Hx D1; lia
            | intros Hd; let Hb := fresh "Hb" in destruct (HOB x ltac:(lia)) as [_ Hb]; apply Hb; sc_cell_img x Hx ].

(* g_nout := no' + m and m bytes Bm copied to g_out + no': aout_at with Bm sent *)
Lemma aout_at_copy : forall ly S (W : world SEGS) mem mem' ev O' Bm mx no' cap out m,
aout_at B RG ly S W mem (CTL 3 0 0 0 ev) O' mx no' cap out ->
0 < m -> no' + m <= cap -> Z.of_nat (length Bm) = m ->
(forall a, 0 <= a < alloc_ceiling -> ~ (rg_nout RG <= a < rg_nout RG + 8) -> ~ (out + no' <= a < out + no' + m) ->
   abyte_kept W mem W mem' a) ->
val_mem SEGS (arm W mem') (rg_nout RG) 8 (no' + m) -> awr W mem' (rg_nout RG) 8 ->
garr8 SEGS (arm W mem') (out + no') (bzs Bm) ->
(forall a, out <= a < out + cap -> 0 <= a < alloc_ceiling /\ ~ in_img SEGS a) ->
aout_at B RG ly S W mem' (CTL 3 0 0 0 ev) (O' ++ Bm) mx (no' + m) cap out.
Proof.
intros ly S W mem mem' ev O' Bm mx no' cap out m
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) Hm Hcap HBm HK Vn Wn HG8 HOB.
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in *.
pose proof sc_errno_img as HERRI.
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
pose proof (pa_obj_img 11 ltac:(lia)) as Q11. pose proof (pa_obj_img 12 ltac:(lia)) as Q12.
pose proof (pa_obj_img 14 ltac:(lia)) as Q14. pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
rewrite HV9 in Q9. rewrite HV10 in Q10. rewrite HV11 in Q11. rewrite HV12 in Q12.
rewrite HV14 in Q14. rewrite HV15 in Q15.
assert (Hno0 : 0 <= no') by lia.
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W mem); [sc_kl HK 6%nat HSM HOB | exact H1]|].
split; [apply (akept_awr W mem); [sc_kl HK 6%nat HSM HOB | exact H2]|].
split; [exact Vn|]. split; [exact Wn|].
split; [apply (akept_vm W mem); [sc_kl HK 8%nat Q14 HOB | exact H5]|].
split; [apply (akept_awr W mem); [sc_kl HK 8%nat Q14 HOB | exact H6]|].
split; [apply (akept_vm W mem); [sc_kl HK 9%nat Q15 HOB | exact H7]|].
split; [apply (akept_awr W mem); [sc_kl HK 9%nat Q15 HOB | exact H8]|].
split; [apply (akept_vm W mem); [sc_kl HK 2%nat Q9 HOB | exact H9]|].
split; [apply (akept_awr W mem); [sc_kl HK 2%nat Q9 HOB | exact H10]|].
split; [apply (akept_vm W mem); [sc_kl HK 3%nat Q10 HOB | exact H11]|].
split; [apply (akept_awr W mem); [sc_kl HK 3%nat Q10 HOB | exact H12]|].
split; [apply (akept_vm W mem); [sc_kl HK 5%nat Q12 HOB | exact H13]|].
split; [apply (akept_awr W mem); [sc_kl HK 5%nat Q12 HOB | exact H14]|].
split; [apply (akept_vm W mem); [sc_kl HK 4%nat Q11 HOB | exact H15]|].
split; [apply (akept_awr W mem); [sc_kl HK 4%nat Q11 HOB | exact H16]|].
split; [apply (akept_vm W mem); [sc_kl HK 10%nat HERRI HOB | exact H17]|].
split; [apply (akept_awr W mem); [sc_kl HK 10%nat HERRI HOB | exact H18]|].
split; [exact H19|]. split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
split; [exact H24|].
split; [rewrite length_app, Nat2Z.inj_add; lia|].
destruct H26 as [(Hc0 & _ & _) | (Hc & Hno & Hin & junk & Hj & Hg)]; [lia|].
right. split; [lia|]. split; [lia|]. split; [exact Hin|].
exists (skipn (Z.to_nat m) junk). split; [rewrite length_skipn; lia|].
unfold bzs in Hg, HG8 |- *. rewrite map_app in Hg. rewrite !map_app, <- app_assoc.
apply garr8_app in Hg as [HgO Hgj].
rewrite <- (firstn_skipn (Z.to_nat m) junk) in Hgj. rewrite map_app in Hgj. apply garr8_app in Hgj as [_ Hgj2].
rewrite !length_map, length_firstn in Hgj2.
replace (Init.Nat.min (Z.to_nat m) (length junk)) with (Z.to_nat m) in Hgj2 by lia.
apply garr8_app. split.
- apply (akept_garr8 W mem); [|exact HgO]. intros x Hx. rewrite length_map in Hx.
  destruct (HOB x ltac:(lia)) as [Hx1 Hx2].
  apply HK; [exact Hx1 | intros Hn; apply Hx2; sc_cell_img x Hn | clear - Hx H25; lia].
- rewrite length_map. apply garr8_app. split.
  + replace (out + Z.of_nat (length O')) with (out + no') by lia. exact HG8.
  + rewrite length_map.
    replace (out + Z.of_nat (length O') + Z.of_nat (length Bm)) with (out + Z.of_nat (length O') + Z.of_nat (Z.to_nat m))
      by lia.
    apply (akept_garr8 W mem); [|exact Hgj2]. intros x Hx. rewrite length_map, length_skipn in Hx.
    destruct (HOB x ltac:(lia)) as [Hx1 Hx2].
    apply HK; [exact Hx1 | intros Hn; apply Hx2; sc_cell_img x Hn | clear - Hx H25 Hm; lia].
Qed.

(* The control flags at a live controller (W_send_line_loop.v). *)
Lemma sc_live_true : forall c len, ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> 0 < len -> sl_live c len = true.
Proof.
intros c len Hcl Hbr Hdd Hlen. unfold sl_live, send_line_c.send_live, send_line_c.send_off.
rewrite Hcl, Hbr, Hdd, (proj2 (Z.eqb_neq len 0)) by lia. reflexivity.
Qed.
Lemma sc_ctl_on : forall c len, ct_cl c = 3 -> ct_br c = 0 -> 0 < len ->
sl_ctl c len = CTL 3 (ct_dd c) (ct_dd c) 0
  (if ct_dd c =? 1 then send_line_c.EPIPE_V else if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c).
Proof.
intros c len Hcl Hbr Hlen. unfold sl_ctl, send_line_c.send_off.
rewrite Hcl, Hbr, (proj2 (Z.eqb_neq len 0)) by lia. reflexivity.
Qed.

Lemma sc_aout_blks_in : forall ly S W mem c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W mem c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.
(* ---- The exit: the epilogue, then sl_post from the concrete facts at 0x828f8 (W_send_line_loop.v sl_exit). ---- *)
Lemma sc_exit_x : forall regsE ly S Hp W mem md c O mx no cap out Bl lyX SX HpX WX regsX memX mdX k out' rest kr,
ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyX SX HpX WX memX mdX k ->
spZ regsX = spZ regsE - SL_FRAME -> getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (spZ regsE - SL_FRAME) regsE ->
apres_kept B W mem WX memX ->
mo_le MT S SX (sl_cost MT c mx no cap (Z.of_nat (length Bl))) ->
rp_RM RP SX kr ->
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) ->
Permutation (ablocks B lyX SX) (aout_blks (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ++ rest) ->
aout_at B RG lyX SX WX memX (sl_ctl c (Z.of_nat (length Bl))) (sl_O c O Bl) mx (sl_no c no (Z.of_nat (length Bl)))
  (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ->
(sl_live c (Z.of_nat (length Bl)) = false -> out' = out) ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX)
(sl_post_x B PST ARx MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr).
Proof.
intros regsE ly S Hp W mem md c O mx no cap out Bl lyX SX HpX WX regsX memX mdX k out' rest kr HJ Hsp H3 H4 Hra HSV HAPK
  HMLE HRM HP1 HP2 HOUT HOFF.
apply (sl_epi_x B PST ARx RG LAWS HG W ly S Hp mem md (spZ regsE) _ lyX SX HpX WX regsX memX mdX k regsE _ HJ eq_refl Hsp H3 H4 Hra HSV).
intros regs' mem' md' HP Hm' HJ'.
assert (GRX : mem_grows (mrestrict (w_H WX) memX) (mrestrict (w_H WX) mem')) by (intros x Hx; rewrite Hm'; exact Hx).
exists lyX, SX, HpX, regs', mem', md', k, out'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP|].
split; [intros a H1 H2 H3' Hpa; exact (apresent_grows _ _ _ _ GRX (HAPK a H1 H2 H3' Hpa))|].
split; [exact HMLE|].
split; [exact HRM|].
split; [exists rest; split; [exact HP1 | exact HP2]|].
split; [|exact HOFF].
apply (aout_at_kept B RG lyX SX WX memX lyX SX WX mem' _ _ _ _ _ _ HOUT); [|intros b Hb; exact (sc_aout_blks_in _ _ _ _ _ _ _ _ _ _ HOUT b Hb)].
intros r _ a _. split.
- exact (aview_eq_of SEGS (w_H WX) memX mem' a (Hm' _)).
- unfold arm. apply writable_kept. intros Hpa. exact (apresent_grows _ _ _ _ GRX Hpa).
Qed.

Lemma sc_map_firstn : forall {X Y : Type} (f : X -> Y) l m, map f (firstn m l) = firstn m (map f l).
Proof. intros X Y f l. induction l as [|x l IH]; intros [|m]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma sc_map_skipn : forall {X Y : Type} (f : X -> Y) l k, map f (skipn k l) = skipn k (map f l).
Proof. intros X Y f l. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
(* An image atom's word (W_send_line_loop.v ew_img). *)
Lemma sc_ew_img : forall E k, img_env VAL A_LIM E -> (A_TEXT <= k < A_LIM)%nat -> ew E k = Z_to_bv 64 (VAL k).
Proof. intros E k HE Hk. rewrite <- (HE k Hk). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Theorem sl_copy_x : sl_copy_stmt_x B PST ARx MT RP MMAX RG.
Proof.
intros n0 regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr IH HM Hb.
unfold SLM_x in HM. cbv zeta in HM.
destruct HM as (lyM & SM & HpM & kM & evL & capM & outM & spent & rest &
  HJ & Hsp & H3 & H4 & Hgp & Htp & HraE & HR & M8 & M16 & HSV & Hcl & Hbr & Hdd & Hsent & Hn & Hev &
  HOUT & Hroom & HGL & Hline0 & Hline1 & HROM & HLOK & HLG & Hcapq & HMM & HLM & HAPK & HMOK & HMLE & HCOST &
  HPerm0 & HPerm1 & HFR & HRMR & HCNT).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresM & HstkM & _).
pose proof HstkM as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresM.
assert (WS : SL_STK = 16512) by reflexivity.
assert (HSF : SL_FRAME = 128) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vcl, Vbr, Vdd, Vei, Vev, Rev, Hclr, Hbrr, Hddr, Heir.
set (len := Z.of_nat (length Bl)) in *.
assert (Hn1 : 0 < n <= len - sent) by (rewrite Hn; apply sc_n_range; lia).
rewrite length_app in HlenO. rewrite Nat2Z.inj_add in HlenO.
assert (HnoS : 0 <= no + sent) by lia.
destruct Hblk as [(Hc0 & _ & _) | (Hcp & Hncap & Hin & junk & Hjunk & Hgout)]; [lia|].
destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memM mdM outM capM HARM Hin) as (Ho16 & Ho4096 & Hoceil & Hoapp & Hopres & _).
assert (Hrq : req_size capM = capM) by (unfold req_size; destruct (Z.eqb_spec capM 0); lia).
rewrite Hrq in Hoceil, Hoapp, Hopres.
pose proof (BLKM lyM SM HpM WM memM mdM outM capM HARM Hin) as HoMAX.
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
pose proof (pa_obj_img 11 ltac:(lia)) as Q11. pose proof (pa_obj_img 12 ltac:(lia)) as Q12.
pose proof (pa_obj_img 13 ltac:(lia)) as Q13. pose proof (pa_obj_img 14 ltac:(lia)) as Q14.
pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
assert (Hlen : len = Z.of_nat (length Bl)) by reflexivity.
(* g_out's block holds no image byte (the client-image law), so no cell of the walk and no read-only byte is in it *)
assert (BLKI : forall a, outM <= a < outM + capM -> ~ in_img SEGS a).
{ intros a Ha. destruct (alx_client_img _ _ _ LAWS lyM SM HpM WM memM mdM a HARM) as (_ & Himg).
  { left. exists outM, capM. split; [exact Hin|]. rewrite Hrq. lia. }
  exact Himg. }
assert (HSTKC : forall a, 0 <= a < alloc_ceiling -> ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME))
  by (intros a Ha; clear - Ha Hceil Hslo WS HSF HES; lia).
(* every byte of the line lies below alloc_ceiling and outside g_out's block *)
assert (LINE : forall a, line <= a < line + len -> 0 <= a < alloc_ceiling /\ ~ (outM <= a < outM + capM)).
{ intros a Ha.
  destruct HLOK as [HL0 | [(q & m & Hq & Hqo & Hq1 & Hq2) | (Hrimg & Hash & Hrst)]].
  - lia.
  - destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memM mdM q m HARM Hq) as (_ & Hq4096 & Hqceil & _ & _ & _).
    pose proof (sep_blocks_x SEGS B ARx LAWS lyM SM HpM WM memM mdM q m outM capM HARM Hq Hin
      ltac:(intros Hx; injection Hx as Hx _; exact (Hqo Hx))) as Dq.
    unfold zdisjoint in Dq. cbn [fst snd] in Dq. rewrite Hrq in Dq. lia.
  - pose proof (pa_img_range _ (Hrimg a Ha)) as HXI.
    split; [lia | intros Hx; exact (BLKI a Hx (Hrimg a Ha))]. }
(* the line's bytes [line + sent, line + sent + n): what AMEMCPY asks of a source, in any AR state at lyM SM *)
assert (LSRC : forall (memT : word -> option byte) mdT, ARx lyM SM HpM WM memT mdT ->
  amem_range (line + sent) n /\ range_addressable (aview SEGS (w_H WM) memT) SHADOW_OFF (line + sent) n /\
  shadow_hull_vis (aview SEGS (w_H WM) memT) (line + sent) n /\
  (outM + (no + sent) + n <= line + sent \/ line + sent + n <= outM + (no + sent)) /\
  (forall a, line + sent <= a < line + sent + n -> 0 <= a < alloc_ceiling)).
{ intros memT mdT HART.
  destruct HLOK as [HL0 | [(q & m & Hq & Hqo & Hq1 & Hq2) | (Hrimg & Hash & Hrst)]].
  - lia.
  - destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memT mdT q m HART Hq) as (_ & Hq4096 & Hqceil & _ & _ & _).
    pose proof (sep_blocks_x SEGS B ARx LAWS lyM SM HpM WM memT mdT q m outM capM HART Hq Hin
      ltac:(intros Hx; injection Hx as Hx _; exact (Hqo Hx))) as Dq.
    unfold zdisjoint in Dq. cbn [fst snd] in Dq. rewrite Hrq in Dq.
    split; [eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS lyM SM HpM WM memT mdT q m); [exact HART | exact Hq | lia | lia]|].
    split; [eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM memT mdT q m);
      [exact HART | exact Hq | lia | lia]|].
    split; [eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM memT mdT q m);
      [exact HART | exact Hq | lia | lia | lia]|].
    split; [lia|]. intros a Ha. lia.
  - assert (HIL : forall a, line + sent <= a < line + sent + n -> 0x10000 <= a < 0x5fb000)
      by (intros a Ha; apply pa_img_range; apply Hrimg; lia).
    pose proof (HIL (line + sent) ltac:(lia)) as HIL0. pose proof (HIL (line + sent + n - 1) ltac:(lia)) as HIL1.
    split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
    destruct (Hash lyM SM HpM WM memT mdT HART) as [Hra Hhv].
    split; [exact (range_addressable_sub _ _ line len (line + sent) n Hra ltac:(lia) ltac:(lia))|].
    split; [exact (sc_hull_sub _ line len (line + sent) n (Hhv ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))|].
    split.
    { (* two non-empty ranges, one of image bytes, one inside g_out's block, are disjoint *)
      destruct (Z_le_gt_dec (outM + (no + sent) + n) (line + sent)) as [D1 | D1]; [left; exact D1|].
      destruct (Z_le_gt_dec (line + sent + n) (outM + (no + sent))) as [D2 | D2]; [right; exact D2|].
      exfalso. apply (BLKI (Z.max (line + sent) (outM + (no + sent)))); [lia | apply Hrimg; lia]. }
    intros a Ha. pose proof (HIL a Ha). lia. }
(* the bytes of g_out the round copies to: present, not the allocator's, in any AR state at lyM SM *)
assert (DST : forall (memT : word -> option byte) mdT, ARx lyM SM HpM WM memT mdT ->
  forall a, outM + (no + sent) <= a < outM + (no + sent) + n -> apresent (w_H WM) memT a /\ ~ aowned B lyM SM a).
{ intros memT mdT HART a Ha.
  destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memT mdT outM capM HART Hin) as (_ & _ & _ & _ & HP & _).
  rewrite Hrq in HP. apply HP. lia. }
pose proof (sl_join_entry WM regsM memM (spZ regsE) len line sent n (no + sent) outM
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  Vno Wno Vout ltac:(lia) ltac:(lia)) as HS.
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R18 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
remember (Eimg (Ereg regsM (j_extra (no + sent) outM))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsM 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsM 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsM 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsM 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 18 18%bv eq_refl); exact R18).
assert (E22 : ew E 22 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 22 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = getr regsM 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 0)).
assert (E33 : ew E 33 = w64 outM) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (N13 : VAL 254%nat = rg_nout RG) by exact HV13.
assert (N15 : VAL 256%nat = rg_out RG) by exact HV15.
assert (N22 : VAL 302%nat + 260 = rg_nout RG) by exact HH22.
assert (N24 : VAL 304%nat + 892 = rg_out RG) by exact HH24.
assert (SHOK : sh_ok SEGS BxJ [] E (mrestrict (w_H WM) memM)) by constructor.
(* 0x82850 .. 0x82864: the two loads, the arguments, the jal to __asan_memcpy *)
jrun RUN HS HJ SHOK JBspan.
{ unfold ss_J; cbn [ss_mem]; unfold j_regions, j_nout, j_out.
  apply awr_ok_x_cons_g; [awr_gb BVE (A_OBJ 13) HV13|].
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_nil. }
rename HFr into HFrA, HG0 into HGA. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msA end.
(* what the first run kept: every byte outside g_nout *)
assert (NOUTG : forall a, ~ inG (G_SL B RG) a -> ~ (rg_nout RG <= a < rg_nout RG + 8))
  by (intros a HnG Hx; apply HnG; clear - Hx; ing_tac).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
  aview SEGS (w_H WM) (ms_mem msA) a = aview SEGS (w_H WM) memM a).
{ intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) memM (ms_mem msA) HFrA a Ha). sc_nowr_n BVE Hnn N13 N22. }
pmkst HS.
prreg HS (1%bv : bv 5) RA1. prreg HS (2%bv : bv 5) RA2. prreg HS (3%bv : bv 5) RA3. prreg HS (4%bv : bv 5) RA4.
preg HS (10%bv : bv 5) RA10. preg HS (11%bv : bv 5) RA11. preg HS (12%bv : bv 5) RA12.
(* __asan_memcpy (g_out + no + sent, line + sent, n) *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_SL B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_asan_memcpy)
    (fun a => outM + (no + sent) <= a < outM + (no + sent) + n)
    (fun regs' (mem' : word -> option byte) => getr regs' 10 = w64 (outM + (no + sent)) /\
      forall i, 0 <= i < n -> aview SEGS (w_H WM) mem' (outM + (no + sent) + i) =
        aview SEGS (w_H WM) (ms_mem msA) (line + sent + i))
    WM (ms_regs msA) (ms_mem msA) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out))
    ly S Hp W mem md ([] : list (Z * Z)) lyM SM HpM _ kM (- SL_FRAME) (Z_to_bv 64 (BASE + 1404)) HG eq_refl HJ).
  - unfold spZ at 1. rewrite RA2, Usp. clear. unfold SL_FRAME. lia.
  - unfold SL_FRAME. reflexivity.
  - unfold SL_FRAME. clear. lia.
  - clear. lia.
  - clear. vm_compute. intros Hx. discriminate Hx.
  - rewrite RA3, E3, H3. exact Hgp.
  - rewrite RA4, E4, H4. exact Htp.
  - exact RA1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros a. destruct (Z_le_gt_dec (outM + (no + sent)) a) as [Ha1 | Ha1];
      [destruct (Z_lt_ge_dec a (outM + (no + sent) + n)) as [Ha2 | Ha2]; [left; lia | right; lia] | right; lia].
  - intros a Ha HGa. exfalso.
    destruct (alx_client_img _ _ _ LAWS lyM SM HpM WM memM mdM a HARM) as (_ & Himg).
    { left. exists outM, capM. split; [exact Hin|]. rewrite Hrq. lia. }
    exact (Himg (proj1 (HG a HGa))).
  - intros a Ha _. split; [|clear; lia].
    exact (sc_dest_awr_x ly S lyM SM HpM WM memM mdM cap out capM outM rest SL_STK (spZ regsE) a HARM HPerm0 HPerm1
      ltac:(lia) ltac:(lia)).
  - intros HPRE HSC. pose proof HPRE as (HARA & _).
    assert (Hsp1 : spZ (ms_regs msA) = spZ regsE - SL_FRAME) by (unfold spZ at 1; rewrite RA2, Usp; reflexivity).
    destruct (LSRC _ _ HARA) as (Lmr & Lra & Lhv & Ldisj & Llow).
    eapply SRr_mono.
    { refine (AMEMCPY lyM SM HpM WM (ms_regs msA) (ms_mem msA) _ (outM + (no + sent)) (line + sent) n HPRE
        _ _ _ _ _ _ _ _ _ _ _ _).
      - rewrite RA10, (sc_add_atoms E 32 33 (no + sent) outM E32 E33) by lia. f_equal. lia.
      - rewrite RA11, (sc_add_atoms E 9 22 line sent E9 E22) by lia. reflexivity.
      - rewrite RA12. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E18.
      - lia.
      - lia.
      - lia.
      - intros a Ha. destruct (DST _ _ HARA a Ha) as [Hpa Hno].
        split; [exact (apresent_writable SEGS _ _ _ Hpa)|]. split; [exact Hno|].
        rewrite Hsp1. apply HSTKC. lia.
      - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS lyM SM HpM WM (ms_mem msA) _ outM capM);
        [exact HARA | exact Hin | lia | rewrite Hrq; lia].
      - (* QMm W1: the destination is g_out's block, a client byte, so it is off the image and holds no kept byte *)
        intros a Ha HK.
        destruct (alx_client_img _ _ _ LAWS lyM SM HpM WM (ms_mem msA) _ a HARA) as (_ & Himg).
        { left. exists outM, capM. split; [exact Hin|]. rewrite Hrq. lia. }
        exact (Himg (proj1 HK)).
      - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM (ms_mem msA) _ outM capM);
        [exact HARA | exact Hin | lia | rewrite Hrq; lia].
      - intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM (ms_mem msA) _ outM capM);
        [exact HARA | exact Hin | lia | rewrite Hrq; lia | exact Hpos].
      - split; [lia|]. split; [lia|]. split.
        + intros a Ha. split.
          * rewrite (KA a ltac:(lia) (NOUTG a (HLG a ltac:(lia)))).
            unfold aview. replace a with (line + Z.of_nat (Z.to_nat (a - line))) by lia.
            rewrite (garr8_mbyte SEGS (mrestrict (w_H WM) memM) line _ (Z.to_nat (a - line)) HGL)
              by (unfold bzs; rewrite length_map; lia).
            discriminate.
          * rewrite Hsp1. apply HSTKC. exact (Llow a Ha).
        + split; [exact Ldisj|]. split; [exact Lmr|]. split; [exact Lra | intros _; exact Lhv]. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
    split; [split; [exact Hres | exact Heff]|].
    split; [intros a Ha HW Hs; exact (Hfr a Ha HW Hs) | exact Hpres2]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (Hres & Hcpy) & Hfr2 & Hpres2).
(* ---- after __asan_memcpy: the two cells kept, the a-registers havocked ---- *)
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H WM) mem2) HP2 [0;1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H WM) (ms_mem msA) mem2 254 (rg_nout RG));
      [rewrite (HEI 254%nat ltac:(cbv; lia)); exact N13 | | exact Hpres2].
    intros a Ha. apply Hfr2; [clear - Ha Q13 HV13; lia
      | intros Hw; cbv beta in Hw; apply (BLKI a); [clear - Hw Hroom Hn1 HnoS; lia
        | exact (proj1 (HG a ltac:(clear - Ha HV13 N13; solve [ing_tac])))]
      | clear - Ha Q13 HV13 QSP C1 HSF HES; lia].
  - apply (region_kept_aview E (w_H WM) (ms_mem msA) mem2 256 (rg_out RG));
      [rewrite (HEI 256%nat ltac:(cbv; lia)); exact N15 | | exact Hpres2].
    intros a Ha. apply Hfr2; [clear - Ha Q15 HV15; lia
      | intros Hw; cbv beta in Hw; apply (BLKI a); [clear - Hw Hroom Hn1 HnoS; lia
        | exact (proj1 (HG a ltac:(clear - Ha HV15 N15; solve [ing_tac])))]
      | clear - Ha Q15 HV15 QSP C1 HSF HES; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 38)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (BVEa : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
assert (HREL : VAL (A_OBJ 13) = VAL (A_HI 22) + 260) by (rewrite HV13, <- HH22; reflexivity).
prebase HS 0%nat (A_HI 22) 260 HREL.
assert (SHOKa : sh_ok SEGS BxJ [] Ea (mrestrict (w_H WM) mem2)) by constructor.
(* 0x82868 .. 0x828a8: g_nout := no + sent + n; the bltz and beqz on n (decided by its fact); sent += n *)
jrun RUN HS HJ2 SHOKa JBspan.
{ apply awr_ok_x_cons_g; [awr_gb BVEa 302%nat N22|].
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_nil. }
rename HFr into HFrB, HG0 into HGB. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msB end.
assert (F18 : ew Ea 18 = w64 n) by (rewrite OLDa by lia; exact E18).
assert (F22 : ew Ea 22 = w64 sent) by (rewrite OLDa by lia; exact E22).
assert (F8 : ew Ea 8 = w64 len) by (rewrite OLDa by lia; exact E8).
assert (U1 : U Ea (SAlu ALU_ADD (SOff 18 0) (SOff 22 0)) = n + sent)
  by (rewrite U_SAlu, (U_atom Ea 18 n F18), (U_atom Ea 22 sent F22) by lia; cbn [zalu_raw]; apply zcanon_id; unfold M64; lia).
assert (U2 : U Ea (SOff 8 0) = len) by (apply (U_atom Ea 8 len F8); lia).
assert (F32 : ew Ea 32 = w64 (no + sent)) by (rewrite OLDa by lia; exact E32).
(* ---- what the copy half leaves, at any memory the last run leaves ---- *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
  aview SEGS (w_H WM) (ms_mem msB) a = aview SEGS (w_H WM) mem2 a).
{ intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) mem2 (ms_mem msB) HFrB a Ha). sc_nowr_n BVEa Hnn N13 N22. }
assert (HOB : forall a, outM <= a < outM + capM -> 0 <= a < alloc_ceiling /\ ~ in_img SEGS a)
  by (intros a Ha; split; [lia | exact (BLKI a Ha)]).
assert (FINAL : forall memF : word -> option byte,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
     aview SEGS (w_H WM) memF a = aview SEGS (w_H WM) (ms_mem msB) a) ->
  mem_grows (mrestrict (w_H WM) (ms_mem msB)) (mrestrict (w_H WM) memF) ->
  val_mem SEGS (arm WM memF) (rg_nout RG) 8 (no + sent + n) ->
  aout_at B RG lyM SM WM memF (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat (sent + n)) Bl) mx (no + sent + n) capM outM /\
  garr8 SEGS (arm WM memF) line (bzs Bl) /\ rom_view SEGS WM memF /\ apres_kept B W mem WM memF /\
  val_mem SEGS (mrestrict (w_H WM) memF) (spZ regsE - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
  val_mem SEGS (mrestrict (w_H WM) memF) (spZ regsE - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
  sl_saved WM memF (spZ regsE - SL_FRAME) regsE).
{ intros memF KF GF VnF.
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
    ~ (outM + (no + sent) <= a < outM + (no + sent) + n) ->
    ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME) ->
    aview SEGS (w_H WM) memF a = aview SEGS (w_H WM) memM a).
  { intros a Ha Hnn Hnd Hns. rewrite (KF a Ha Hnn), (KB a Ha Hnn).
    rewrite (Hfr2 a Ha Hnd ltac:(clear - Hns; lia)). exact (KA a Ha Hnn). }
  assert (PRF : forall a, apresent (w_H WM) memM a -> apresent (w_H WM) memF a).
  { intros a Hpa. apply (apresent_grows _ _ _ _ GF). apply (apresent_grows _ _ _ _ HGB).
    apply Hpres2. apply (apresent_grows _ _ _ _ HGA). exact Hpa. }
  assert (WRF : forall a, writable_at SEGS (arm WM memM) a -> writable_at SEGS (arm WM memF) a)
    by (intros a Hw; unfold arm in *; exact (writable_kept (w_H WM) memM memF a (PRF a) Hw)).
  assert (NNO : forall a, outM <= a < outM + capM -> ~ (rg_nout RG <= a < rg_nout RG + 8))
    by (intros a Ha Hx; apply (BLKI a Ha); exact (proj1 (HG a ltac:(clear - Hx; solve [ing_tac])))).
  assert (LENBM : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat sent) Bl))) = n)
    by (rewrite length_firstn, length_skipn; lia).
  assert (HG8 : garr8 SEGS (arm WM memF) (outM + (no + sent)) (bzs (firstn (Z.to_nat n) (skipn (Z.to_nat sent) Bl)))).
  { unfold bzs. rewrite sc_map_firstn, sc_map_skipn.
    apply (sc_garr8_copy WM memM memF line (outM + (no + sent)) (map bz Bl) (Z.to_nat sent) (Z.to_nat n) HGL).
    - rewrite length_map. lia.
    - intros j Hj.
      rewrite (KF (outM + (no + sent) + j) ltac:(lia) (NNO (outM + (no + sent) + j) ltac:(lia))).
      rewrite (KB (outM + (no + sent) + j) ltac:(lia) (NNO (outM + (no + sent) + j) ltac:(lia))).
      rewrite (Hcpy j ltac:(lia)).
      rewrite (KA (line + sent + j) ltac:(lia) (NOUTG (line + sent + j) (HLG (line + sent + j) ltac:(lia)))).
      f_equal. lia. }
  pose proof (aout_at_copy lyM SM WM memM memF evL (O ++ firstn (Z.to_nat sent) Bl)
    (firstn (Z.to_nat n) (skipn (Z.to_nat sent) Bl)) mx (no + sent) capM outM n HOUT ltac:(lia) ltac:(lia) LENBM)
    as AO.
  specialize (AO ltac:(intros a Ha Hnn Hnd; split;
      [apply KALL; [lia | exact Hnn | exact Hnd | apply HSTKC; exact Ha] | exact (WRF a)])).
  specialize (AO VnF ltac:(intros i Hi; apply WRF; exact (Wno i Hi)) HG8 HOB).
  rewrite <- app_assoc, <- sc_firstn_add, <- Z2Nat.inj_add in AO by lia.
  split; [exact AO|].
  split.
  { apply (akept_garr8 WM memM WM memF); [|exact HGL]. intros x Hx. unfold bzs in Hx. rewrite length_map in Hx.
    destruct (LINE x ltac:(lia)) as [Hx1 Hx2].
    split; [apply KALL; [lia | exact (NOUTG x (HLG x ltac:(lia))) | clear - Hx2 Hroom Hn1 HnoS; lia
      | apply HSTKC; exact Hx1] | exact (WRF x)]. }
  split.
  { intros a Ha. pose proof Ha as (sg & Hsg & _ & Hr).
    assert (HIa : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range _ HIa) as HXI.
    rewrite KALL; [exact (HROM a Ha) | lia | | intros Hx; apply (BLKI a); [clear - Hx Hroom Hn1 HnoS; lia | exact HIa]
      | apply HSTKC; lia].
    intros Hx. apply (HGR a); [clear - Hx; ing_tac | exact Ha]. }
  split; [intros a H1 H2 H3' Hpa; exact (PRF a (HAPK a H1 H2 H3' Hpa))|].
  split; [apply (sc_vm_keep WM memM memF); [intros x Hx; apply KALL;
    clear - Hx QSP C1 Q13 HV13 Hoceil Hroom Hn1 HnoS HSF HES Hceil Hslo WS; lia | exact M8]|].
  split; [apply (sc_vm_keep WM memM memF); [intros x Hx; apply KALL;
    clear - Hx QSP C1 Q13 HV13 Hoceil Hroom Hn1 HnoS HSF HES Hceil Hslo WS; lia | exact M16]|].
  intros i Hi. apply (sc_vm_keep WM memM memF); [|exact (HSV i Hi)].
  intros x Hx. apply KALL; clear - Hx Hi QSP C1 Q13 HV13 Hoceil Hroom Hn1 HnoS HSF HES Hceil Hslo WS; lia. }
(* 0x828a8 bltu s6,s0 *)
psrr_branch_tok RUN BR HS SHOKa JBspan.
- (* sent + n < len: back to the loop head L, with the bound one smaller *)
  rewrite branch_ltu_U, U1, U2 in Hc. apply Z.ltb_lt in Hc.
  jrun_to RUNTO HS HJ2 SHOKa JBspan A_sl_loop.
  { apply awr_ok_x_cons_g; [awr_gb BVEa 302%nat N22|].
    apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_nil. }
  rename HFr into HFrC, HG0 into HGC. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msF end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
    aview SEGS (w_H WM) (ms_mem msF) a = aview SEGS (w_H WM) (ms_mem msB) a).
  { intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) (ms_mem msB) (ms_mem msF) HFrC a Ha). sc_nowr_n BVEa Hnn N13 N22. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF' =>
    pose proof (st_ok_pi_region_nth Ev ssF msF' 0 _ HS eq_refl) as RG0 end.
  cbn [ms_mem restrict] in RG0.
  assert (VnF : val_mem SEGS (arm WM (ms_mem msF)) (rg_nout RG) 8 (no + sent + n)).
  { rewrite <- N22. replace (no + sent + n) with (n + (no + sent)) by lia.
    exact (field_of_region Ea _ 302%nat _ _ _ _ _ _ 260 8 (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) (n + (no + sent)) RG0
      (HEIa 302%nat ltac:(cbv; lia)) (or_introl eq_refl)
      (sc_add_atoms Ea 18 32 n (no + sent) F18 F32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)). }
  destruct (FINAL (ms_mem msF) KF HGC VnF) as (AOF & GLF & ROMF & APKF & M8F & M16F & HSVF).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. preg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HRLF : sl_regsL (ms_regs msF) len line (sent + n)).
  { unfold sl_regsL.
    rewrite P8, P9, P19, P22, P23, P20, P21, P24, P25, P26, P27.
    rewrite (OLDa 8%nat ltac:(clia)), (OLDa 9%nat ltac:(clia)), (OLDa 23%nat ltac:(clia)).
    rewrite E8, E9, E23, R23.
    rewrite (sc_add_atoms Ea 18 22 n sent F18 F22 ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_comm.
    rewrite !(sc_ew_img _ _ HEIa) by (cbv; lia).
    repeat split; reflexivity. }
  assert (HSPF : spZ (ms_regs msF) = spZ regsE - SL_FRAME).
  { unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp. }
  assert (HR3F : getr (ms_regs msF) 3 = getr regsE 3) by (rewrite P3, (OLDa 3%nat ltac:(clia)), E3; exact H3).
  assert (HR4F : getr (ms_regs msF) 4 = getr regsE 4) by (rewrite P4, (OLDa 4%nat ltac:(clia)), E4; exact H4).
  assert (EQ1 : no + (sent + n) = no + sent + n) by lia.
  assert (EQ2 : len - (sent + n) = len - sent - n) by lia.
  apply (IH regsE ly S Hp W mem md c O mx no cap out line Bl WM (ms_regs msF) (ms_mem msF) _ (sent + n) 0 kr).
  2: { fold len. rewrite Nat2Z.inj_succ in Hb. lia. }
  unfold SLI_x. cbv zeta. fold len.
  exists lyM, SM, HpM, kM, evL, capM, outM, spent, rest.
  split; [exact HJ2|]. split; [exact HSPF|]. split; [exact HR3F|]. split; [exact HR4F|].
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|]. split; [exact HRLF|].
  split; [exact M8F|]. split; [exact M16F|]. split; [exact HSVF|].
  split; [exact Hcl|]. split; [exact Hbr|]. split; [lia|].
  split; [right; reflexivity|]. split; [intros _; reflexivity|]. split; [intros Hx; lia|].
  split; [rewrite Hev; destruct (ct_ei c =? 1); reflexivity|].
  split; [rewrite Hdd, EQ1; exact AOF|].
  split; [exact GLF|]. split; [exact Hline0|]. split; [exact Hline1|]. split; [exact ROMF|].
  split; [exact HLOK|]. split; [exact HLG|].
  split; [intros _; rewrite EQ1, EQ2; exact Hcapq|]. split; [intros Hx; lia|].
  split; [intros _; rewrite EQ1, EQ2; exact HMM|]. split; [intros _; rewrite EQ1, EQ2; exact HLM|].
  split; [exact APKF|]. split; [exact HMOK|]. split; [exact HMLE|].
  split; [intros _; rewrite EQ1, EQ2; exact HCOST|]. split; [intros Hx; lia|].
  split; [exact HPerm0|]. split; [exact HPerm1|]. split; [exact HFR|].
  split; [intros _; rewrite EQ1, EQ2; exact HRMR|]. split; [intros Hx; lia|]. exact HCNT.
- (* sent + n = len: out through the epilogue *)
  rewrite branch_ltu_U, U1, U2 in Hc. apply Z.ltb_ge in Hc.
  assert (Hfin : sent + n = len) by lia.
  jrun_to RUNTO HS HJ2 SHOKa JBspan A_sl_epi.
  { apply awr_ok_x_cons_g; [awr_gb BVEa 302%nat N22|].
    apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_nil. }
  rename HFr into HFrC, HG0 into HGC. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msF end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
    aview SEGS (w_H WM) (ms_mem msF) a = aview SEGS (w_H WM) (ms_mem msB) a).
  { intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) (ms_mem msB) (ms_mem msF) HFrC a Ha). sc_nowr_n BVEa Hnn N13 N22. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF' =>
    pose proof (st_ok_pi_region_nth Ev ssF msF' 0 _ HS eq_refl) as RG0 end.
  cbn [ms_mem restrict] in RG0.
  assert (VnF : val_mem SEGS (arm WM (ms_mem msF)) (rg_nout RG) 8 (no + sent + n)).
  { rewrite <- N22. replace (no + sent + n) with (n + (no + sent)) by lia.
    exact (field_of_region Ea _ 302%nat _ _ _ _ _ _ 260 8 (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) (n + (no + sent)) RG0
      (HEIa 302%nat ltac:(cbv; lia)) (or_introl eq_refl)
      (sc_add_atoms Ea 18 32 n (no + sent) F18 F32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)). }
  destruct (FINAL (ms_mem msF) KF HGC VnF) as (AOF & GLF & ROMF & APKF & M8F & M16F & HSVF).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  change (BASE + 1548) with (BASE + A_sl_epi).
  assert (HCAPF : sl_cap c mx no cap len = capM)
    by (rewrite Hcapq; replace (len - sent - n) with 0 by lia; reflexivity).
  apply (sc_exit_x regsE ly S Hp W mem md c O mx no cap out Bl lyM SM HpM WM (ms_regs msF) (ms_mem msF) _ kM outM rest kr
    HJ2);
    fold len.
  + unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp.
  + rewrite P3, (OLDa 3%nat ltac:(clia)), E3. exact H3.
  + rewrite P4, (OLDa 4%nat ltac:(clia)), E4. exact H4.
  + exact HraE.
  + exact HSVF.
  + exact APKF.
  + apply (mle_weaken MT S SM spent _ MTL HMLE).
    replace (len - sent - n) with 0 in HCOST by lia. change (Z.to_nat 0) with 0%nat in HCOST.
    cbn [sl_cost_run] in HCOST. lia.
  + (* the room: the rounds after this one are none, so the post's kr is under the join's budget *)
    eapply RMM_of; [|exact HRMR]. clear - HRMR. lia.
  + exact HPerm0.
  + rewrite HCAPF. exact HPerm1.
  + rewrite (sc_ctl_on c len Hcl Hbr ltac:(lia)), Hdd, HCAPF.
    replace (if 0 =? 1 then send_line_c.EPIPE_V else if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c)
      with evL by (rewrite Hev; reflexivity).
    unfold sl_O, sl_no. rewrite (sc_live_true c len Hcl Hbr Hdd ltac:(lia)).
    rewrite (sc_live_true c (Z.of_nat (length Bl)) Hcl Hbr Hdd ltac:(lia)).
    rewrite Hfin, Hlen, Nat2Z.id, firstn_all in AOF.
    replace (no + len) with (no + sent + n) by lia. exact AOF.
  + (* the copy path is a live send: the off conjunct holds vacuously *)
    intros Hoff. exfalso.
    rewrite sc_live_true in Hoff by (first [exact Hcl | exact Hbr | exact Hdd | lia]). discriminate Hoff.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this Section's texts at a world relation R.  Each <name>_xR below is <name>_x
   with the journal ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, sl_post_x / sl_spec_x -> their R
   twins (W_send_line_xR.v, R right after ARx), every carrier or walk it names -> its R twin, and the walk on
   W_journal_x.v's G chain (RUNG / RUNTOG, W_kit_x.v's paj_run_tok_xR / paj_run_to_tok_xR, W_kit.v's paj_branch_xR
   as BRR, SRrG_bind / SRrG_mono / SRrG_ret); every other token is the strict text's.  At R := wle each is its strict twin by conversion. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* W_send_line_datab_x.v:591 sc_exit_x at R *)
Lemma sc_exit_xR : forall regsE ly S Hp W mem md c O mx no cap out Bl lyX SX HpX WX regsX memX mdX k out' rest kr,
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyX SX HpX WX memX mdX k ->
spZ regsX = spZ regsE - SL_FRAME -> getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (spZ regsE - SL_FRAME) regsE ->
apres_kept B W mem WX memX ->
mo_le MT S SX (sl_cost MT c mx no cap (Z.of_nat (length Bl))) ->
rp_RM RP SX kr ->
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) ->
Permutation (ablocks B lyX SX) (aout_blks (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ++ rest) ->
aout_at B RG lyX SX WX memX (sl_ctl c (Z.of_nat (length Bl))) (sl_O c O Bl) mx (sl_no c no (Z.of_nat (length Bl)))
  (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ->
(sl_live c (Z.of_nat (length Bl)) = false -> out' = out) ->
SRrG SEGS R WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX)
(sl_post_xR B PST ARx R MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr).
Proof.
intros regsE ly S Hp W mem md c O mx no cap out Bl lyX SX HpX WX regsX memX mdX k out' rest kr HJ Hsp H3 H4 Hra HSV HAPK
  HMLE HRM HP1 HP2 HOUT HOFF.
apply (sl_epi_xR B PST ARx RG LAWS HG R WLE_R W ly S Hp mem md (spZ regsE) _ lyX SX HpX WX regsX memX mdX k regsE _ HJ eq_refl Hsp H3 H4 Hra HSV).
intros regs' mem' md' HP Hm' HJ'.
assert (GRX : mem_grows (mrestrict (w_H WX) memX) (mrestrict (w_H WX) mem')) by (intros x Hx; rewrite Hm'; exact Hx).
exists lyX, SX, HpX, regs', mem', md', k, out'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP|].
split; [intros a H1 H2 H3' Hpa; exact (apresent_grows _ _ _ _ GRX (HAPK a H1 H2 H3' Hpa))|].
split; [exact HMLE|].
split; [exact HRM|].
split; [exists rest; split; [exact HP1 | exact HP2]|].
split; [|exact HOFF].
apply (aout_at_kept B RG lyX SX WX memX lyX SX WX mem' _ _ _ _ _ _ HOUT); [|intros b Hb; exact (sc_aout_blks_in _ _ _ _ _ _ _ _ _ _ HOUT b Hb)].
intros r _ a _. split.
- exact (aview_eq_of SEGS (w_H WX) memX mem' a (Hm' _)).
- unfold arm. apply writable_kept. intros Hpa. exact (apresent_grows _ _ _ _ GRX Hpa).
Qed.
(* W_send_line_datab_x.v:633 sl_copy_x at R *)
Theorem sl_copy_xR : sl_copy_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros n0 regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr IH HM Hb.
unfold SLM_xR in HM. cbv zeta in HM.
destruct HM as (lyM & SM & HpM & kM & evL & capM & outM & spent & rest &
  HJ & Hsp & H3 & H4 & Hgp & Htp & HraE & HR & M8 & M16 & HSV & Hcl & Hbr & Hdd & Hsent & Hn & Hev &
  HOUT & Hroom & HGL & Hline0 & Hline1 & HROM & HLOK & HLG & Hcapq & HMM & HLM & HAPK & HMOK & HMLE & HCOST &
  HPerm0 & HPerm1 & HFR & HRMR & HCNT).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresM & HstkM & _).
pose proof HstkM as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresM.
assert (WS : SL_STK = 16512) by reflexivity.
assert (HSF : SL_FRAME = 128) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vcl, Vbr, Vdd, Vei, Vev, Rev, Hclr, Hbrr, Hddr, Heir.
set (len := Z.of_nat (length Bl)) in *.
assert (Hn1 : 0 < n <= len - sent) by (rewrite Hn; apply sc_n_range; lia).
rewrite length_app in HlenO. rewrite Nat2Z.inj_add in HlenO.
assert (HnoS : 0 <= no + sent) by lia.
destruct Hblk as [(Hc0 & _ & _) | (Hcp & Hncap & Hin & junk & Hjunk & Hgout)]; [lia|].
destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memM mdM outM capM HARM Hin) as (Ho16 & Ho4096 & Hoceil & Hoapp & Hopres & _).
assert (Hrq : req_size capM = capM) by (unfold req_size; destruct (Z.eqb_spec capM 0); lia).
rewrite Hrq in Hoceil, Hoapp, Hopres.
pose proof (BLKM lyM SM HpM WM memM mdM outM capM HARM Hin) as HoMAX.
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
pose proof (pa_obj_img 11 ltac:(lia)) as Q11. pose proof (pa_obj_img 12 ltac:(lia)) as Q12.
pose proof (pa_obj_img 13 ltac:(lia)) as Q13. pose proof (pa_obj_img 14 ltac:(lia)) as Q14.
pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
assert (Hlen : len = Z.of_nat (length Bl)) by reflexivity.
(* g_out's block holds no image byte (the client-image law), so no cell of the walk and no read-only byte is in it *)
assert (BLKI : forall a, outM <= a < outM + capM -> ~ in_img SEGS a).
{ intros a Ha. destruct (alx_client_img _ _ _ LAWS lyM SM HpM WM memM mdM a HARM) as (_ & Himg).
  { left. exists outM, capM. split; [exact Hin|]. rewrite Hrq. lia. }
  exact Himg. }
assert (HSTKC : forall a, 0 <= a < alloc_ceiling -> ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME))
  by (intros a Ha; clear - Ha Hceil Hslo WS HSF HES; lia).
(* every byte of the line lies below alloc_ceiling and outside g_out's block *)
assert (LINE : forall a, line <= a < line + len -> 0 <= a < alloc_ceiling /\ ~ (outM <= a < outM + capM)).
{ intros a Ha.
  destruct HLOK as [HL0 | [(q & m & Hq & Hqo & Hq1 & Hq2) | (Hrimg & Hash & Hrst)]].
  - lia.
  - destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memM mdM q m HARM Hq) as (_ & Hq4096 & Hqceil & _ & _ & _).
    pose proof (sep_blocks_x SEGS B ARx LAWS lyM SM HpM WM memM mdM q m outM capM HARM Hq Hin
      ltac:(intros Hx; injection Hx as Hx _; exact (Hqo Hx))) as Dq.
    unfold zdisjoint in Dq. cbn [fst snd] in Dq. rewrite Hrq in Dq. lia.
  - pose proof (pa_img_range _ (Hrimg a Ha)) as HXI.
    split; [lia | intros Hx; exact (BLKI a Hx (Hrimg a Ha))]. }
(* the line's bytes [line + sent, line + sent + n): what AMEMCPY asks of a source, in any AR state at lyM SM *)
assert (LSRC : forall (memT : word -> option byte) mdT, ARx lyM SM HpM WM memT mdT ->
  amem_range (line + sent) n /\ range_addressable (aview SEGS (w_H WM) memT) SHADOW_OFF (line + sent) n /\
  shadow_hull_vis (aview SEGS (w_H WM) memT) (line + sent) n /\
  (outM + (no + sent) + n <= line + sent \/ line + sent + n <= outM + (no + sent)) /\
  (forall a, line + sent <= a < line + sent + n -> 0 <= a < alloc_ceiling)).
{ intros memT mdT HART.
  destruct HLOK as [HL0 | [(q & m & Hq & Hqo & Hq1 & Hq2) | (Hrimg & Hash & Hrst)]].
  - lia.
  - destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memT mdT q m HART Hq) as (_ & Hq4096 & Hqceil & _ & _ & _).
    pose proof (sep_blocks_x SEGS B ARx LAWS lyM SM HpM WM memT mdT q m outM capM HART Hq Hin
      ltac:(intros Hx; injection Hx as Hx _; exact (Hqo Hx))) as Dq.
    unfold zdisjoint in Dq. cbn [fst snd] in Dq. rewrite Hrq in Dq.
    split; [eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS lyM SM HpM WM memT mdT q m); [exact HART | exact Hq | lia | lia]|].
    split; [eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM memT mdT q m);
      [exact HART | exact Hq | lia | lia]|].
    split; [eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM memT mdT q m);
      [exact HART | exact Hq | lia | lia | lia]|].
    split; [lia|]. intros a Ha. lia.
  - assert (HIL : forall a, line + sent <= a < line + sent + n -> 0x10000 <= a < 0x5fb000)
      by (intros a Ha; apply pa_img_range; apply Hrimg; lia).
    pose proof (HIL (line + sent) ltac:(lia)) as HIL0. pose proof (HIL (line + sent + n - 1) ltac:(lia)) as HIL1.
    split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
    destruct (Hash lyM SM HpM WM memT mdT HART) as [Hra Hhv].
    split; [exact (range_addressable_sub _ _ line len (line + sent) n Hra ltac:(lia) ltac:(lia))|].
    split; [exact (sc_hull_sub _ line len (line + sent) n (Hhv ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))|].
    split.
    { (* two non-empty ranges, one of image bytes, one inside g_out's block, are disjoint *)
      destruct (Z_le_gt_dec (outM + (no + sent) + n) (line + sent)) as [D1 | D1]; [left; exact D1|].
      destruct (Z_le_gt_dec (line + sent + n) (outM + (no + sent))) as [D2 | D2]; [right; exact D2|].
      exfalso. apply (BLKI (Z.max (line + sent) (outM + (no + sent)))); [lia | apply Hrimg; lia]. }
    intros a Ha. pose proof (HIL a Ha). lia. }
(* the bytes of g_out the round copies to: present, not the allocator's, in any AR state at lyM SM *)
assert (DST : forall (memT : word -> option byte) mdT, ARx lyM SM HpM WM memT mdT ->
  forall a, outM + (no + sent) <= a < outM + (no + sent) + n -> apresent (w_H WM) memT a /\ ~ aowned B lyM SM a).
{ intros memT mdT HART a Ha.
  destruct (alx_blocks _ _ _ LAWS lyM SM HpM WM memT mdT outM capM HART Hin) as (_ & _ & _ & _ & HP & _).
  rewrite Hrq in HP. apply HP. lia. }
pose proof (sl_join_entry WM regsM memM (spZ regsE) len line sent n (no + sent) outM
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  Vno Wno Vout ltac:(lia) ltac:(lia)) as HS.
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R18 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
remember (Eimg (Ereg regsM (j_extra (no + sent) outM))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsM 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsM 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsM 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsM 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 18 18%bv eq_refl); exact R18).
assert (E22 : ew E 22 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsM _ 22 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = getr regsM 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsM _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 0)).
assert (E33 : ew E 33 = w64 outM) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (N13 : VAL 254%nat = rg_nout RG) by exact HV13.
assert (N15 : VAL 256%nat = rg_out RG) by exact HV15.
assert (N22 : VAL 302%nat + 260 = rg_nout RG) by exact HH22.
assert (N24 : VAL 304%nat + 892 = rg_out RG) by exact HH24.
assert (SHOK : sh_ok SEGS BxJ [] E (mrestrict (w_H WM) memM)) by constructor.
(* 0x82850 .. 0x82864: the two loads, the arguments, the jal to __asan_memcpy *)
jrun RUNG HS HJ SHOK JBspan.
{ unfold ss_J; cbn [ss_mem]; unfold j_regions, j_nout, j_out.
  apply awr_ok_x_cons_g; [awr_gb BVE (A_OBJ 13) HV13|].
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_nil. }
rename HFr into HFrA, HG0 into HGA. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msA end.
(* what the first run kept: every byte outside g_nout *)
assert (NOUTG : forall a, ~ inG (G_SL B RG) a -> ~ (rg_nout RG <= a < rg_nout RG + 8))
  by (intros a HnG Hx; apply HnG; clear - Hx; ing_tac).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
  aview SEGS (w_H WM) (ms_mem msA) a = aview SEGS (w_H WM) memM a).
{ intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) memM (ms_mem msA) HFrA a Ha). sc_nowr_n BVE Hnn N13 N22. }
pmkst HS.
prreg HS (1%bv : bv 5) RA1. prreg HS (2%bv : bv 5) RA2. prreg HS (3%bv : bv 5) RA3. prreg HS (4%bv : bv 5) RA4.
preg HS (10%bv : bv 5) RA10. preg HS (11%bv : bv 5) RA11. preg HS (12%bv : bv 5) RA12.
(* __asan_memcpy (g_out + no + sent, line + sent, n) *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_SL B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_asan_memcpy)
    (fun a => outM + (no + sent) <= a < outM + (no + sent) + n)
    (fun regs' (mem' : word -> option byte) => getr regs' 10 = w64 (outM + (no + sent)) /\
      forall i, 0 <= i < n -> aview SEGS (w_H WM) mem' (outM + (no + sent) + i) =
        aview SEGS (w_H WM) (ms_mem msA) (line + sent + i))
    WM (ms_regs msA) (ms_mem msA) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out))
    ly S Hp W mem md ([] : list (Z * Z)) lyM SM HpM _ kM (- SL_FRAME) (Z_to_bv 64 (BASE + 1404)) HG eq_refl HJ).
  - unfold spZ at 1. rewrite RA2, Usp. clear. unfold SL_FRAME. lia.
  - unfold SL_FRAME. reflexivity.
  - unfold SL_FRAME. clear. lia.
  - clear. lia.
  - clear. vm_compute. intros Hx. discriminate Hx.
  - rewrite RA3, E3, H3. exact Hgp.
  - rewrite RA4, E4, H4. exact Htp.
  - exact RA1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros a. destruct (Z_le_gt_dec (outM + (no + sent)) a) as [Ha1 | Ha1];
      [destruct (Z_lt_ge_dec a (outM + (no + sent) + n)) as [Ha2 | Ha2]; [left; lia | right; lia] | right; lia].
  - intros a Ha HGa. exfalso.
    destruct (alx_client_img _ _ _ LAWS lyM SM HpM WM memM mdM a HARM) as (_ & Himg).
    { left. exists outM, capM. split; [exact Hin|]. rewrite Hrq. lia. }
    exact (Himg (proj1 (HG a HGa))).
  - intros a Ha _. split; [|clear; lia].
    exact (sc_dest_awr_x ly S lyM SM HpM WM memM mdM cap out capM outM rest SL_STK (spZ regsE) a HARM HPerm0 HPerm1
      ltac:(lia) ltac:(lia)).
  - intros HPRE HSC. pose proof HPRE as (HARA & _).
    assert (Hsp1 : spZ (ms_regs msA) = spZ regsE - SL_FRAME) by (unfold spZ at 1; rewrite RA2, Usp; reflexivity).
    destruct (LSRC _ _ HARA) as (Lmr & Lra & Lhv & Ldisj & Llow).
    (* the memcpy entry contract (aj_gx_entry_at_xR's premise) stays strict: SRr_mono *)
    eapply SRr_mono.
    { refine (AMEMCPY lyM SM HpM WM (ms_regs msA) (ms_mem msA) _ (outM + (no + sent)) (line + sent) n HPRE
        _ _ _ _ _ _ _ _ _ _ _ _).
      - rewrite RA10, (sc_add_atoms E 32 33 (no + sent) outM E32 E33) by lia. f_equal. lia.
      - rewrite RA11, (sc_add_atoms E 9 22 line sent E9 E22) by lia. reflexivity.
      - rewrite RA12. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E18.
      - lia.
      - lia.
      - lia.
      - intros a Ha. destruct (DST _ _ HARA a Ha) as [Hpa Hno].
        split; [exact (apresent_writable SEGS _ _ _ Hpa)|]. split; [exact Hno|].
        rewrite Hsp1. apply HSTKC. lia.
      - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS lyM SM HpM WM (ms_mem msA) _ outM capM);
        [exact HARA | exact Hin | lia | rewrite Hrq; lia].
      - (* QMm W1: the destination is g_out's block, a client byte, so it is off the image and holds no kept byte *)
        intros a Ha HK.
        destruct (alx_client_img _ _ _ LAWS lyM SM HpM WM (ms_mem msA) _ a HARA) as (_ & Himg).
        { left. exists outM, capM. split; [exact Hin|]. rewrite Hrq. lia. }
        exact (Himg (proj1 HK)).
      - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM (ms_mem msA) _ outM capM);
        [exact HARA | exact Hin | lia | rewrite Hrq; lia].
      - intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 lyM SM HpM WM (ms_mem msA) _ outM capM);
        [exact HARA | exact Hin | lia | rewrite Hrq; lia | exact Hpos].
      - split; [lia|]. split; [lia|]. split.
        + intros a Ha. split.
          * rewrite (KA a ltac:(lia) (NOUTG a (HLG a ltac:(lia)))).
            unfold aview. replace a with (line + Z.of_nat (Z.to_nat (a - line))) by lia.
            rewrite (garr8_mbyte SEGS (mrestrict (w_H WM) memM) line _ (Z.to_nat (a - line)) HGL)
              by (unfold bzs; rewrite length_map; lia).
            discriminate.
          * rewrite Hsp1. apply HSTKC. exact (Llow a Ha).
        + split; [exact Ldisj|]. split; [exact Lmr|]. split; [exact Lra | intros _; exact Lhv]. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
    split; [split; [exact Hres | exact Heff]|].
    split; [intros a Ha HW Hs; exact (Hfr a Ha HW Hs) | exact Hpres2]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (Hres & Hcpy) & Hfr2 & Hpres2).
(* ---- after __asan_memcpy: the two cells kept, the a-registers havocked ---- *)
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H WM) mem2) HP2 [0;1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H WM) (ms_mem msA) mem2 254 (rg_nout RG));
      [rewrite (HEI 254%nat ltac:(cbv; lia)); exact N13 | | exact Hpres2].
    intros a Ha. apply Hfr2; [clear - Ha Q13 HV13; lia
      | intros Hw; cbv beta in Hw; apply (BLKI a); [clear - Hw Hroom Hn1 HnoS; lia
        | exact (proj1 (HG a ltac:(clear - Ha HV13 N13; solve [ing_tac])))]
      | clear - Ha Q13 HV13 QSP C1 HSF HES; lia].
  - apply (region_kept_aview E (w_H WM) (ms_mem msA) mem2 256 (rg_out RG));
      [rewrite (HEI 256%nat ltac:(cbv; lia)); exact N15 | | exact Hpres2].
    intros a Ha. apply Hfr2; [clear - Ha Q15 HV15; lia
      | intros Hw; cbv beta in Hw; apply (BLKI a); [clear - Hw Hroom Hn1 HnoS; lia
        | exact (proj1 (HG a ltac:(clear - Ha HV15 N15; solve [ing_tac])))]
      | clear - Ha Q15 HV15 QSP C1 HSF HES; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 38)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (BVEa : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
assert (HREL : VAL (A_OBJ 13) = VAL (A_HI 22) + 260) by (rewrite HV13, <- HH22; reflexivity).
prebase HS 0%nat (A_HI 22) 260 HREL.
assert (SHOKa : sh_ok SEGS BxJ [] Ea (mrestrict (w_H WM) mem2)) by constructor.
(* 0x82868 .. 0x828a8: g_nout := no + sent + n; the bltz and beqz on n (decided by its fact); sent += n *)
jrun RUNG HS HJ2 SHOKa JBspan.
{ apply awr_ok_x_cons_g; [awr_gb BVEa 302%nat N22|].
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_nil. }
rename HFr into HFrB, HG0 into HGB. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msB end.
assert (F18 : ew Ea 18 = w64 n) by (rewrite OLDa by lia; exact E18).
assert (F22 : ew Ea 22 = w64 sent) by (rewrite OLDa by lia; exact E22).
assert (F8 : ew Ea 8 = w64 len) by (rewrite OLDa by lia; exact E8).
assert (U1 : U Ea (SAlu ALU_ADD (SOff 18 0) (SOff 22 0)) = n + sent)
  by (rewrite U_SAlu, (U_atom Ea 18 n F18), (U_atom Ea 22 sent F22) by lia; cbn [zalu_raw]; apply zcanon_id; unfold M64; lia).
assert (U2 : U Ea (SOff 8 0) = len) by (apply (U_atom Ea 8 len F8); lia).
assert (F32 : ew Ea 32 = w64 (no + sent)) by (rewrite OLDa by lia; exact E32).
(* ---- what the copy half leaves, at any memory the last run leaves ---- *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
  aview SEGS (w_H WM) (ms_mem msB) a = aview SEGS (w_H WM) mem2 a).
{ intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) mem2 (ms_mem msB) HFrB a Ha). sc_nowr_n BVEa Hnn N13 N22. }
assert (HOB : forall a, outM <= a < outM + capM -> 0 <= a < alloc_ceiling /\ ~ in_img SEGS a)
  by (intros a Ha; split; [lia | exact (BLKI a Ha)]).
assert (FINAL : forall memF : word -> option byte,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
     aview SEGS (w_H WM) memF a = aview SEGS (w_H WM) (ms_mem msB) a) ->
  mem_grows (mrestrict (w_H WM) (ms_mem msB)) (mrestrict (w_H WM) memF) ->
  val_mem SEGS (arm WM memF) (rg_nout RG) 8 (no + sent + n) ->
  aout_at B RG lyM SM WM memF (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat (sent + n)) Bl) mx (no + sent + n) capM outM /\
  garr8 SEGS (arm WM memF) line (bzs Bl) /\ rom_view SEGS WM memF /\ apres_kept B W mem WM memF /\
  val_mem SEGS (mrestrict (w_H WM) memF) (spZ regsE - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
  val_mem SEGS (mrestrict (w_H WM) memF) (spZ regsE - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
  sl_saved WM memF (spZ regsE - SL_FRAME) regsE).
{ intros memF KF GF VnF.
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
    ~ (outM + (no + sent) <= a < outM + (no + sent) + n) ->
    ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME) ->
    aview SEGS (w_H WM) memF a = aview SEGS (w_H WM) memM a).
  { intros a Ha Hnn Hnd Hns. rewrite (KF a Ha Hnn), (KB a Ha Hnn).
    rewrite (Hfr2 a Ha Hnd ltac:(clear - Hns; lia)). exact (KA a Ha Hnn). }
  assert (PRF : forall a, apresent (w_H WM) memM a -> apresent (w_H WM) memF a).
  { intros a Hpa. apply (apresent_grows _ _ _ _ GF). apply (apresent_grows _ _ _ _ HGB).
    apply Hpres2. apply (apresent_grows _ _ _ _ HGA). exact Hpa. }
  assert (WRF : forall a, writable_at SEGS (arm WM memM) a -> writable_at SEGS (arm WM memF) a)
    by (intros a Hw; unfold arm in *; exact (writable_kept (w_H WM) memM memF a (PRF a) Hw)).
  assert (NNO : forall a, outM <= a < outM + capM -> ~ (rg_nout RG <= a < rg_nout RG + 8))
    by (intros a Ha Hx; apply (BLKI a Ha); exact (proj1 (HG a ltac:(clear - Hx; solve [ing_tac])))).
  assert (LENBM : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat sent) Bl))) = n)
    by (rewrite length_firstn, length_skipn; lia).
  assert (HG8 : garr8 SEGS (arm WM memF) (outM + (no + sent)) (bzs (firstn (Z.to_nat n) (skipn (Z.to_nat sent) Bl)))).
  { unfold bzs. rewrite sc_map_firstn, sc_map_skipn.
    apply (sc_garr8_copy WM memM memF line (outM + (no + sent)) (map bz Bl) (Z.to_nat sent) (Z.to_nat n) HGL).
    - rewrite length_map. lia.
    - intros j Hj.
      rewrite (KF (outM + (no + sent) + j) ltac:(lia) (NNO (outM + (no + sent) + j) ltac:(lia))).
      rewrite (KB (outM + (no + sent) + j) ltac:(lia) (NNO (outM + (no + sent) + j) ltac:(lia))).
      rewrite (Hcpy j ltac:(lia)).
      rewrite (KA (line + sent + j) ltac:(lia) (NOUTG (line + sent + j) (HLG (line + sent + j) ltac:(lia)))).
      f_equal. lia. }
  pose proof (aout_at_copy lyM SM WM memM memF evL (O ++ firstn (Z.to_nat sent) Bl)
    (firstn (Z.to_nat n) (skipn (Z.to_nat sent) Bl)) mx (no + sent) capM outM n HOUT ltac:(lia) ltac:(lia) LENBM)
    as AO.
  specialize (AO ltac:(intros a Ha Hnn Hnd; split;
      [apply KALL; [lia | exact Hnn | exact Hnd | apply HSTKC; exact Ha] | exact (WRF a)])).
  specialize (AO VnF ltac:(intros i Hi; apply WRF; exact (Wno i Hi)) HG8 HOB).
  rewrite <- app_assoc, <- sc_firstn_add, <- Z2Nat.inj_add in AO by lia.
  split; [exact AO|].
  split.
  { apply (akept_garr8 WM memM WM memF); [|exact HGL]. intros x Hx. unfold bzs in Hx. rewrite length_map in Hx.
    destruct (LINE x ltac:(lia)) as [Hx1 Hx2].
    split; [apply KALL; [lia | exact (NOUTG x (HLG x ltac:(lia))) | clear - Hx2 Hroom Hn1 HnoS; lia
      | apply HSTKC; exact Hx1] | exact (WRF x)]. }
  split.
  { intros a Ha. pose proof Ha as (sg & Hsg & _ & Hr).
    assert (HIa : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range _ HIa) as HXI.
    rewrite KALL; [exact (HROM a Ha) | lia | | intros Hx; apply (BLKI a); [clear - Hx Hroom Hn1 HnoS; lia | exact HIa]
      | apply HSTKC; lia].
    intros Hx. apply (HGR a); [clear - Hx; ing_tac | exact Ha]. }
  split; [intros a H1 H2 H3' Hpa; exact (PRF a (HAPK a H1 H2 H3' Hpa))|].
  split; [apply (sc_vm_keep WM memM memF); [intros x Hx; apply KALL;
    clear - Hx QSP C1 Q13 HV13 Hoceil Hroom Hn1 HnoS HSF HES Hceil Hslo WS; lia | exact M8]|].
  split; [apply (sc_vm_keep WM memM memF); [intros x Hx; apply KALL;
    clear - Hx QSP C1 Q13 HV13 Hoceil Hroom Hn1 HnoS HSF HES Hceil Hslo WS; lia | exact M16]|].
  intros i Hi. apply (sc_vm_keep WM memM memF); [|exact (HSV i Hi)].
  intros x Hx. apply KALL; clear - Hx Hi QSP C1 Q13 HV13 Hoceil Hroom Hn1 HnoS HSF HES Hceil Hslo WS; lia. }
(* 0x828a8 bltu s6,s0 *)
psrr_branch_tok RUNG BRR HS SHOKa JBspan.
- (* sent + n < len: back to the loop head L, with the bound one smaller *)
  rewrite branch_ltu_U, U1, U2 in Hc. apply Z.ltb_lt in Hc.
  jrun_to RUNTOG HS HJ2 SHOKa JBspan A_sl_loop.
  { apply awr_ok_x_cons_g; [awr_gb BVEa 302%nat N22|].
    apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_nil. }
  rename HFr into HFrC, HG0 into HGC. clear HF.
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msF end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
    aview SEGS (w_H WM) (ms_mem msF) a = aview SEGS (w_H WM) (ms_mem msB) a).
  { intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) (ms_mem msB) (ms_mem msF) HFrC a Ha). sc_nowr_n BVEa Hnn N13 N22. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF' =>
    pose proof (st_ok_pi_region_nth Ev ssF msF' 0 _ HS eq_refl) as RG0 end.
  cbn [ms_mem restrict] in RG0.
  assert (VnF : val_mem SEGS (arm WM (ms_mem msF)) (rg_nout RG) 8 (no + sent + n)).
  { rewrite <- N22. replace (no + sent + n) with (n + (no + sent)) by lia.
    exact (field_of_region Ea _ 302%nat _ _ _ _ _ _ 260 8 (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) (n + (no + sent)) RG0
      (HEIa 302%nat ltac:(cbv; lia)) (or_introl eq_refl)
      (sc_add_atoms Ea 18 32 n (no + sent) F18 F32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)). }
  destruct (FINAL (ms_mem msF) KF HGC VnF) as (AOF & GLF & ROMF & APKF & M8F & M16F & HSVF).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. preg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HRLF : sl_regsL (ms_regs msF) len line (sent + n)).
  { unfold sl_regsL.
    rewrite P8, P9, P19, P22, P23, P20, P21, P24, P25, P26, P27.
    rewrite (OLDa 8%nat ltac:(clia)), (OLDa 9%nat ltac:(clia)), (OLDa 23%nat ltac:(clia)).
    rewrite E8, E9, E23, R23.
    rewrite (sc_add_atoms Ea 18 22 n sent F18 F22 ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_comm.
    rewrite !(sc_ew_img _ _ HEIa) by (cbv; lia).
    repeat split; reflexivity. }
  assert (HSPF : spZ (ms_regs msF) = spZ regsE - SL_FRAME).
  { unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp. }
  assert (HR3F : getr (ms_regs msF) 3 = getr regsE 3) by (rewrite P3, (OLDa 3%nat ltac:(clia)), E3; exact H3).
  assert (HR4F : getr (ms_regs msF) 4 = getr regsE 4) by (rewrite P4, (OLDa 4%nat ltac:(clia)), E4; exact H4).
  assert (EQ1 : no + (sent + n) = no + sent + n) by lia.
  assert (EQ2 : len - (sent + n) = len - sent - n) by lia.
  apply (IH regsE ly S Hp W mem md c O mx no cap out line Bl WM (ms_regs msF) (ms_mem msF) _ (sent + n) 0 kr).
  2: { fold len. rewrite Nat2Z.inj_succ in Hb. lia. }
  unfold SLI_xR. cbv zeta. fold len.
  exists lyM, SM, HpM, kM, evL, capM, outM, spent, rest.
  split; [exact HJ2|]. split; [exact HSPF|]. split; [exact HR3F|]. split; [exact HR4F|].
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|]. split; [exact HRLF|].
  split; [exact M8F|]. split; [exact M16F|]. split; [exact HSVF|].
  split; [exact Hcl|]. split; [exact Hbr|]. split; [lia|].
  split; [right; reflexivity|]. split; [intros _; reflexivity|]. split; [intros Hx; lia|].
  split; [rewrite Hev; destruct (ct_ei c =? 1); reflexivity|].
  split; [rewrite Hdd, EQ1; exact AOF|].
  split; [exact GLF|]. split; [exact Hline0|]. split; [exact Hline1|]. split; [exact ROMF|].
  split; [exact HLOK|]. split; [exact HLG|].
  split; [intros _; rewrite EQ1, EQ2; exact Hcapq|]. split; [intros Hx; lia|].
  split; [intros _; rewrite EQ1, EQ2; exact HMM|]. split; [intros _; rewrite EQ1, EQ2; exact HLM|].
  split; [exact APKF|]. split; [exact HMOK|]. split; [exact HMLE|].
  split; [intros _; rewrite EQ1, EQ2; exact HCOST|]. split; [intros Hx; lia|].
  split; [exact HPerm0|]. split; [exact HPerm1|]. split; [exact HFR|].
  split; [intros _; rewrite EQ1, EQ2; exact HRMR|]. split; [intros Hx; lia|]. exact HCNT.
- (* sent + n = len: out through the epilogue *)
  rewrite branch_ltu_U, U1, U2 in Hc. apply Z.ltb_ge in Hc.
  assert (Hfin : sent + n = len) by lia.
  jrun_to RUNTOG HS HJ2 SHOKa JBspan A_sl_epi.
  { apply awr_ok_x_cons_g; [awr_gb BVEa 302%nat N22|].
    apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_nil. }
  rename HFr into HFrC, HG0 into HGC. clear HF.
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msF end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nout RG <= a < rg_nout RG + 8) ->
    aview SEGS (w_H WM) (ms_mem msF) a = aview SEGS (w_H WM) (ms_mem msB) a).
  { intros a Ha Hnn. apply (aview_kept_out _ _ (w_H WM) (ms_mem msB) (ms_mem msF) HFrC a Ha). sc_nowr_n BVEa Hnn N13 N22. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF' =>
    pose proof (st_ok_pi_region_nth Ev ssF msF' 0 _ HS eq_refl) as RG0 end.
  cbn [ms_mem restrict] in RG0.
  assert (VnF : val_mem SEGS (arm WM (ms_mem msF)) (rg_nout RG) 8 (no + sent + n)).
  { rewrite <- N22. replace (no + sent + n) with (n + (no + sent)) by lia.
    exact (field_of_region Ea _ 302%nat _ _ _ _ _ _ 260 8 (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) (n + (no + sent)) RG0
      (HEIa 302%nat ltac:(cbv; lia)) (or_introl eq_refl)
      (sc_add_atoms Ea 18 32 n (no + sent) F18 F32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)). }
  destruct (FINAL (ms_mem msF) KF HGC VnF) as (AOF & GLF & ROMF & APKF & M8F & M16F & HSVF).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  change (BASE + 1548) with (BASE + A_sl_epi).
  assert (HCAPF : sl_cap c mx no cap len = capM)
    by (rewrite Hcapq; replace (len - sent - n) with 0 by lia; reflexivity).
  apply (sc_exit_xR regsE ly S Hp W mem md c O mx no cap out Bl lyM SM HpM WM (ms_regs msF) (ms_mem msF) _ kM outM rest kr
    HJ2);
    fold len.
  + unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp.
  + rewrite P3, (OLDa 3%nat ltac:(clia)), E3. exact H3.
  + rewrite P4, (OLDa 4%nat ltac:(clia)), E4. exact H4.
  + exact HraE.
  + exact HSVF.
  + exact APKF.
  + apply (mle_weaken MT S SM spent _ MTL HMLE).
    replace (len - sent - n) with 0 in HCOST by lia. change (Z.to_nat 0) with 0%nat in HCOST.
    cbn [sl_cost_run] in HCOST. lia.
  + (* the room: the rounds after this one are none, so the post's kr is under the join's budget *)
    eapply RMM_of; [|exact HRMR]. clear - HRMR. lia.
  + exact HPerm0.
  + rewrite HCAPF. exact HPerm1.
  + rewrite (sc_ctl_on c len Hcl Hbr ltac:(lia)), Hdd, HCAPF.
    replace (if 0 =? 1 then send_line_c.EPIPE_V else if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c)
      with evL by (rewrite Hev; reflexivity).
    unfold sl_O, sl_no. rewrite (sc_live_true c len Hcl Hbr Hdd ltac:(lia)).
    rewrite (sc_live_true c (Z.of_nat (length Bl)) Hcl Hbr Hdd ltac:(lia)).
    rewrite Hfin, Hlen, Nat2Z.id, firstn_all in AOF.
    replace (no + len) with (no + sent + n) by lia. exact AOF.
  + (* the copy path is a live send: the off conjunct holds vacuously *)
    intros Hoff. exfalso.
    rewrite sc_live_true in Hoff by (first [exact Hcl | exact Hbr | exact Hdd | lia]). discriminate Hoff.
Qed.
End wR.
End c.
End b.
End a.
