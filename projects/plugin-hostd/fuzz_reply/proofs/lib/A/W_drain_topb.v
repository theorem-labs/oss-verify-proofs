(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the REST segment of fuzz_reply's drain ASan walk (fuzz_reply.asan
   0x83a4c .. 0x83ab4): s->used = |W| - p, the move-down of the incomplete line to the buffer's start
   (__asan_memmove at 0x83a68) and the long-line reset (s->used = 0, s->skip = 1), back to the outer loop's head.
   The statement is W_drain_cx.v's dr_rest_stmt; the Section header below is that file's, verbatim. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_rest.v, with its module names changed; 3243 of its 3655 lines of code are new or changed and 1881 lines of the source are left out. *)
(* rule 24 reuse search, run once before this file was written:
   the reuse-search script run.sh (sha256 a7c4b196531a; internal record) drain  (stdout: done; its 1276-line report is
   drain.txt (sha256 598fcc6281a0; internal record)): entry A 0x830dc, entry B 0x83278 (static t symbol: no trampoline, no real_f slot), 0 released lemmas at either address; none of its hits is a walk of 0x83314 .. 0x8347c in this lane's W form.
   proves no function (kind: segment lemma) *)
(* The TAIL of fuzz_reply's drain TOP segment (fuzz_reply.asan 0x83314 .. 0x8347c), the statement
   W_drain_topb_cx.v dr_toptail_stmt: from DT2 (the harness slot g_s[j] found) to
     - the EINTR round: g_s[j].eintr = 0 (0x83338), __errno_location (0x8333c, AERRNO), errno = EINTR (0x83358),
       back to DI 0x831f8 in the round state dclr sg;
     - the empty-pending test: g_s[j].pending.n == 0 (0x8337c) -> DEND 0x83bbc;
     - the data round: n = min(v[0].n - pending_off, cap - used) (0x833c0 .. 0x833d0), __asan_memcpy (0x833f4,
       AMEMCPY) of the n bytes into s->buf + s->used, the byte loop's setup -> DRB 0 at 0x8347c.
   The four shadow addresses drain computes as ((g_s + c) >> 3) + s8 (s8 = the shadow base + 12 j) are re-expressed
   before their loads as shadow(&g_s[j] + c) (tt_reseat), so one shadow base (atom 21) folds every check. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_topb_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

(* ---- The symbolic state at DT2 (0x83314). ----
   Atoms beyond the 32 registers (Ereg's extras): 32 = g_s[j].eintr, 33 = g_s[j].pending.n, 34 = the pending
   vector v, 35 = pending_off, 36 = v[0].s, 37 = v[0].n, 38 = the round's n (dnum).  Registers keep their own atoms:
   2 = sp, 18 = g_s, 21 = the shadow base, 22 = SA, 23 = &g_s[j], 24 = the shadow base + 12 j, 10 = s->buf + s->used,
   13 = s->cap - s->used.  The frame region holds the nine slots the tail reads (104 .. 176); the slot g_s[j] holds
   the four fields the tail reads.  The write windows (g_s[j].eintr, the frame slots the data round stores) are
   added on the arm that writes them. *)
#[local] Notation tt_gsh c := (SAlu ALU_SRL (SOff 18 c) (SLit 3)).
#[local] Notation tt_shA m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0)).
Definition TTspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition TT_HI : Z := 140737479966720.
Definition A_tt_sh1 : Z := AF_fr_drain + 0x240.   (* 0x8331c, the shadow load of &g_s[j].eintr *)
Definition A_tt_sh2 : Z := AF_fr_drain + 0x290.   (* 0x8336c, the shadow load of &g_s[j].pending.n *)
Definition A_tt_sh3 : Z := AF_fr_drain + 0x2ac.   (* 0x83388, the store of shadow(&g_s[j].pending) to 80(sp) *)
Definition A_tt_sh4 : Z := AF_fr_drain + 0x2d8.   (* 0x833b4, the store of shadow(&g_s[j].pending_off) to 192(sp) *)
Definition A_tt_n : Z := AF_fr_drain + 0x2f8.     (* 0x833d4, n = min(v[0].n - off, cap - used) in s4 *)
Definition tt_f1 : YP09.region := YP09.mkRegion (Some 2%nat) 88 192 88 88
  [ YP09.mkChunk 104 (CVal 8 (tt_gsh 56)); YP09.mkChunk 112 (CVal 8 (tt_gsh 48));
    YP09.mkChunk 120 (CVal 8 (tt_gsh 40)); YP09.mkChunk 136 (CVal 8 (tt_gsh 16));
    YP09.mkChunk 144 (CVal 8 (tt_gsh 32)); YP09.mkChunk 152 (CVal 8 (tt_gsh 24));
    YP09.mkChunk 160 (CVal 8 (tt_shA 22 32)); YP09.mkChunk 168 (CVal 8 (tt_gsh 12));
    YP09.mkChunk 176 (CVal 8 (tt_shA 22 0)) ].
Definition tt_gs_chunks : list YP09.chunk :=
  [ YP09.mkChunk 12 (CVal 4 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
    YP09.mkChunk 24 (CVal 4 (SOff 33 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0)) ].
Definition tt_g0 : YP09.region := YP09.mkRegion (Some 23%nat) 12 40 12 12 tt_gs_chunks.
Definition tt_IMGF : afact := mkAF 0x10000 0x5fb000 3.
Definition tt_facts0 : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0); (18%nat, tt_IMGF); (23%nat, tt_IMGF);
            (32%nat, mkAF 0 1 0); (33%nat, mkAF 0 (2 ^ 30) 0) ] [] [].
Definition ss_tt : sstate := mkSS A_dr_slot sr_atoms [ tt_f1; tt_g0 ] None tt_facts0.
Definition TT_SH0 : list shent := [ mkSHE 23 0 96 ].
Definition tt_extra (ei n v off s0 l0 dn : Z) : list word := map (Z_to_bv 64) [ei; n; v; off; s0; l0; dn].
(* the data round's added regions: the vector's first record, the frame slots [24, 88) and [192, 208) it stores *)
Definition tt_vec : YP09.region := YP09.mkRegion (Some 34%nat) 0 16 0 0
  [ YP09.mkChunk 0 (CVal 8 (SOff 36 0)); YP09.mkChunk 8 (CVal 8 (SOff 37 0)) ].
Definition tt_f0 : YP09.region := YP09.mkRegion (Some 2%nat) 24 88 24 88 [].
Definition tt_f2 : YP09.region := YP09.mkRegion (Some 2%nat) 192 208 192 208 [].
Definition TT_SHD : list shent := [ mkSHE 23 0 96; mkSHE 34 0 16 ].
(* the head record of a list, (0, []) when it is empty *)
Definition tt_hd (l : hlist) : Z * list byte := match hl_recs l with r :: _ => r | [] => (0, []) end.
(* the harness source with g_s[j].eintr cleared (the EINTR round's store) *)
Definition tt_clr_ei (h : hsrc) : hsrc :=
  HS (hs_fd h) (hs_open h) (hs_closed h) 0 (hs_pending h) (hs_off h) (hs_partial h) (hs_pjunk h) (hs_npartial h)
     (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).
(* the relay entry with new contents after s->used (the data round's __asan_memcpy) *)
Definition tt_junk (e : rentry) (j : list byte) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e) (re_pad2 e)
     (re_keys e) (re_U e) j.

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
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) ->
  p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
  aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- Denotations of the walk's symbolic values. ---- *)
Lemma tt_U_gsh : forall E g c, ew E 18 = Z_to_bv 64 g -> 0 <= g < 2 ^ 64 -> 0 <= g + c < 2 ^ 64 ->
U E (tt_gsh c) = (g + c) / 8.
Proof.
intros E g c Hn Hg Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 18 g c Hn Hg Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma tt_U_shA : forall E m v c, ew E m = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (tt_shA m c) = shadow_addr (v + c).
Proof.
intros E m v c Hn H21 Hv Hc. unfold shadow_addr. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E m v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((v + c) / 8))
  by (unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (U_atom E 21 SHADOW_OFF H21) by (unfold SHADOW_OFF; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma tt_den_gsh : forall E g c, ew E 18 = Z_to_bv 64 g -> 0 <= g < 2 ^ 64 -> 0 <= g + c < 2 ^ 64 ->
sv_denot E (tt_gsh c) = Z_to_bv 64 ((g + c) / 8).
Proof. intros E g c Hn Hg Hc. rewrite denot_lit_U. f_equal. exact (tt_U_gsh E g c Hn Hg Hc). Qed.

Lemma tt_den_shA : forall E m v c, ew E m = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> sv_denot E (tt_shA m c) = Z_to_bv 64 (shadow_addr (v + c)).
Proof. intros E m v c Hn H21 Hv Hc. rewrite denot_lit_U. f_equal. exact (tt_U_shA E m v c Hn H21 Hv Hc). Qed.

Lemma tt_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c Hn Hv Hc. rewrite denot_lit_U. f_equal. exact (U_atom_off E n v c Hn Hv Hc). Qed.

Lemma tt_sh_range : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 64.
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.

(* ((g_s + c) >> 3) + (SB + 12 j) is shadow(&g_s[j] + c): 96 j is 8 * 12 j *)
Lemma tt_den_resh : forall E g j c,
ew E 18 = Z_to_bv 64 g -> ew E 24 = Z_to_bv 64 (SHADOW_OFF + 12 * j) ->
ew E 23 = Z_to_bv 64 (g + 96 * j) -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= g -> 0 <= j -> 0 <= c -> g + 96 * j + c < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (tt_gsh c) (SOff 24 0)) = sv_denot E (tt_shA 23 c).
Proof.
intros E g j c H18 H24 H23 H21 Hg Hj Hc Hb.
rewrite !denot_lit_U. f_equal.
rewrite (tt_U_shA E 23 (g + 96 * j) c H23 H21) by lia.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (tt_U_gsh E g c H18) by lia.
rewrite (U_atom E 24 (SHADOW_OFF + 12 * j) H24) by (unfold SHADOW_OFF; lia).
unfold shadow_addr.
replace (g + 96 * j + c) with ((g + c) + (12 * j) * 8) by lia. rewrite Z.div_add by lia.
assert (Hd : 0 <= (g + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* a register re-expressed by another symbolic value with the same denotation (a Theorem Labs lane's dt_reseat) *)
Lemma tt_reseat : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = sv_denot E e -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
  (ss_facts ss)) ms (sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq.
  cbn [ss_regs] in Hq. rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* a register read off a symbolic state, with its value left as the state's own expression *)
Ltac tt_reg HS r Hr :=
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

Lemma tt_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma tt_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma tt_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply tt_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

(* errno's four bytes lie off g_s (HRGD) *)
Lemma tt_errno_gs : as_errno B + 4 <= rg_s RG \/ rg_s RG + 4 * ASRC <= as_errno B.
Proof.
pose proof (tt_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D.
cbn [nth] in D. unfold zdisj in D. cbn [fst snd] in D. lia.
Qed.

(* no byte is in a region's write window: every region of a read-only stretch has whi <= wlo *)
Lemma tt_nowr : forall E (rs : smem) (x : word),
forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true -> ~ in_wrange E rs (bv_unsigned x).
Proof.
intros E rs x HF (r & Hin & Hr).
rewrite forallb_forall in HF. pose proof (HF r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.

(* the data round's write windows are the frame slots [24, 88) and [192, 208) *)
Definition tt_frw (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  (match YP09.r_base r with Some 2%nat => true | _ => false end &&
   (((24 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 88)) || ((192 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 208)))).
Lemma tt_nowr_fr : forall E (rs : smem) sp y, forallb tt_frw rs = true -> bv_unsigned (ew E 2) = sp ->
~ (sp + 24 <= y < sp + 88) -> ~ (sp + 192 <= y < sp + 208) -> ~ in_wrange E rs y.
Proof.
intros E rs sp y HF Hsp N1 N2 (r & Hin & Hr).
rewrite forallb_forall in HF. pose proof (HF r Hin) as Hq. unfold tt_frw in Hq.
apply orb_prop in Hq as [Hq | Hq]; [apply Z.leb_le in Hq; lia|].
destruct (YP09.r_base r) as [[|[|[|]]]|] eqn:Eb; cbn [andb] in Hq; try discriminate.
cbn [base_val] in Hr. rewrite Hsp in Hr.
apply orb_prop in Hq as [Hq | Hq]; apply andb_prop in Hq as [Q1 Q2]; apply Z.leb_le in Q1, Q2; lia.
Qed.

(* ---- Byte algebra (a Theorem Labs lane's dt_ helpers). ---- *)
Lemma tt_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma tt_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma tt_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof.
intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. reflexivity.
Qed.
Lemma tt_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma tt_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0)))
  by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, tt_nth_zle by exact Hk. rewrite tt_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma tt_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.
Lemma tt_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H KL. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (KL x Hx).
Qed.
Lemma tt_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat)
  by (rewrite tt_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite tt_nth_le_bytes by assumption. reflexivity.
Qed.
Lemma tt_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Ltac tt_len := rewrite ?length_app, ?tt_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes;
  cbn [length].

(* ---- The blocks the cut's representations name are live (a Theorem Labs lane's dt_ helpers). ---- *)
Lemma tt_aentry_blks_in : forall ly S (W : world SEGS) m e,
aentry_okx B ly S W m e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W m e (_ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hkeys) b Hb.
unfold aentry_blks in Hb.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
  + apply in_map_iff in Hb as (k & <- & Hk).
    rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
  + destruct Hb as [<- | Hb].
    * destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
- destruct Hb as [<- | Hb].
  + destruct Hbuf as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
    * destruct Hb as [<- | Hb].
      -- destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
      -- apply in_map_iff in Hb as (k & <- & Hk).
         rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
Qed.

Lemma tt_alist_blks_in : forall ly S (W : world SEGS) m LA l lines,
alist_at B ly S W m LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W m LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
- destruct Hb as [<- | Hb].
  + destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
Qed.

Lemma tt_asrc_blks_in : forall ly S (W : world SEGS) m HA h,
asrc_at B ly S W m HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W m HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
  Hexp & Hheld & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (tt_alist_blks_in ly S W m (HA + 16) (hs_pending h) false Hpend b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (tt_alist_blks_in ly S W m (HA + 64) (hs_expected h) true Hexp b Hb)
  |exact (tt_alist_blks_in ly S W m (HA + 80) (hs_held h) true Hheld b Hb)].
Qed.

Lemma tt_aout_blks_in : forall ly S (W : world SEGS) m c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W m c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.

Lemma tt_aentry_okx_kept : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e,
aentry_okx B ly S W m e -> akept W m W' m' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) -> aentry_okx B ly' S' W' m' e.
Proof.
intros ly S W m ly' S' W' m' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* the memory core of a cut carried across a stretch that stores nothing (a Theorem Labs lane's dt_DMEM_kept) *)
Lemma tt_DMEM_kept : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM B RG cx ly1 S1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 HMEM HJ2 KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (Hkept : forall a, abyte_kept W1 m1 W1 m2 a).
{ intros a. split; [exact (KL a)|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKA : forall fp, akept W1 m1 W1 m2 fp) by (intros fp r Hr a Ha; exact (Hkept a)).
assert (HVM : forall a n v, val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v H. apply (akept_vm W1 m1); [intros x Hx; exact (Hkept x) | exact H]. }
split; [exact HJ2|].
split; [intros a Ha; rewrite (KL a); exact (Hrom a Ha)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & ASV).
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVM; assumption | intros i Hi; apply HVM; exact (ASV i Hi) ]. }
split; [exact (tt_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => KL x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact (tt_aentry_okx_kept ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  (tt_aentry_blks_in ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  (tt_asrc_blks_in ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact (tt_aout_blks_in ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.

(* the pending vector's first record: v[0].s at v, v[0].n at v + 8 *)
Lemma tt_vec_rec : forall (W : world SEGS) m v r0 rs junk,
garr8 SEGS (arm W m) v (bzs (concat (map text_rec (r0 :: rs)) ++ junk)) ->
0 <= fst r0 < 2 ^ 64 -> Z.of_nat (length (snd r0)) < 2 ^ 64 ->
val_mem SEGS (arm W m) v 8 (fst r0) /\ val_mem SEGS (arm W m) (v + 8) 8 (Z.of_nat (length (snd r0))).
Proof.
intros W m v r0 rs junk H H1 H2.
cbn [map concat] in H. unfold text_rec in H. rewrite <- !app_assoc, !tt_bzs_app in H.
apply garr8_app in H as [HA H]. apply garr8_app in H as [HB _].
rewrite (tt_le8_bytes (fst r0) H1) in HA. rewrite (tt_le8_bytes (Z.of_nat (length (snd r0)))) in HB by lia.
split.
- apply (tt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact H1 | exact HA].
- apply (tt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; lia|].
  apply (tt_garr8_at _ _ _ _ HB). tt_len. lia.
Qed.

(* ---- Blocks: two different live blocks are apart; a live block lies off the image (W_drain_rest.v rs_). ---- *)
Lemma tt_pw_in2 : forall {X} (R : X -> X -> Prop) l x y, YG0f.pairwise R l -> In x l -> In y l -> x <> y ->
R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
cbn [In YG0f.pairwise] in HP, Hx, Hy.
destruct HP as [HF HP]. rewrite Forall_forall in HF.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- exfalso; apply Hne; reflexivity.
- left. exact (HF y Hy).
- right. exact (HF x Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.
Lemma tt_pw_nodup : forall l : list (Z * Z), (forall x, In x l -> 1 <= snd x) -> YG0f.pairwise zdisjoint l ->
List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hpw; [apply List.NoDup_nil|].
destruct Hpw as [Hx Hl]. apply List.NoDup_cons.
- intros Hin. rewrite Forall_forall in Hx. pose proof (Hx x Hin) as Hzz. pose proof (Hpos x (or_introl eq_refl)).
  unfold zdisjoint in Hzz. lia.
- apply IH; [intros y Hy; apply Hpos; right; exact Hy | exact Hl].
Qed.
Lemma tt_nodup_map_inj : forall {X Y} (f : X -> Y) (l : list X) x y,
List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros X Y f l. induction l as [|z l IH]; intros x y Hnd Hx Hy Hf; [destruct Hx|].
cbn [map] in Hnd. inversion Hnd as [|w ws Hz Hnd']; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y Hnd' Hx Hy Hf)].
- exfalso. apply Hz. rewrite Hf. apply in_map. exact Hy.
- exfalso. apply Hz. rewrite <- Hf. apply in_map. exact Hx.
Qed.
(* two ranges [p, p + n) and [q, q + m) apart; a Definition, so lia does not case-split it in a large context *)
Definition tt_apart (p n q m : Z) : Prop := p + n <= q \/ q + m <= p.
Lemma tt_blk_apart : forall ly S (W : world SEGS) mem md p n q m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
tt_apart p (req_size n) q (req_size m).
Proof.
intros ly S W mem md p n q m HAR Hp Hq Hne.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
pose proof (tt_pw_nodup _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (tt_nodup_map_inj f _ _ _ Hnd Hp Hq E))).
destruct (tt_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hp) (in_map f _ _ Hq) Hf) as [X|X];
  unfold tt_apart, zdisjoint, f in *; cbn [fst snd] in X; lia.
Qed.
Lemma tt_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hp : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
rewrite <- Eb. exact (NoDup_map_inv f _ (tt_pw_nodup _ Hpos Hpw)).
Qed.
Lemma tt_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & H1 & _ & H3). exists sg. split; [exact H1 | exact H3]. Qed.
Lemma tt_blk_noimg : forall ly S (W : world SEGS) mem md q m a,
AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md q m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl (ex_intro _ q (ex_intro _ m (conj Hin Ha)))))).
Qed.
Lemma tt_amem_range_blk : forall ly S (W : world SEGS) mem md q m a n,
AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> 0 <= n -> a + n <= q + req_size m ->
amem_range a n.
Proof.
intros ly S W mem md q m a n HAR Hin H1 H2 H3.
destruct (al_blocks SEGS B LAWS ly S W mem md q m HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma tt_vm_kept : forall (W : world SEGS) m m' a n v,
(forall k, (k < n)%nat -> aview SEGS (w_H W) m' (a + Z.of_nat k) = aview SEGS (w_H W) m (a + Z.of_nat k)) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v HK Hv k Hk. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat k)); [exact (Hv k Hk) | exact (HK k Hk)].
Qed.
(* s4 = v[0].n - pending_off (0x833c8) *)
Lemma tt_U_sub : forall E (a b : nat) va vb,
bv_unsigned (ew E a) = va -> bv_unsigned (ew E b) = vb -> 0 <= va <= vb -> vb < 2 ^ 63 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit (-1))) (SOff b 0)) = vb - va.
Proof.
intros E a b va vb Ha Hb Hv Hvb.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite !U_SOff, U_SLit, Ha, Hb, !Z.add_0_r.
rewrite (zcanon_id va), (zcanon_id vb) by (unfold M64; lia).
change (zcanon (-1)) with (M64 - 1).
replace (zcanon (va * (M64 - 1))) with (zcanon (- va)).
2:{ unfold zcanon. replace (va * (M64 - 1)) with (- va + va * M64) by lia.
    symmetry. apply Z_mod_plus_full. }
unfold zcanon, M64. rewrite Zplus_mod_idemp_l. replace (- va + vb) with (vb - va) by lia.
apply Z.mod_small. lia.
Qed.

(* ---- The symbolic state at DT2, from the cut's concrete facts. ---- *)
Lemma tt_entry : forall (W : world SEGS) regs m sp SA HA ei n v off s0 l0 dn,
spZ regs = sp -> 2 ^ 46 <= sp -> sp + 336 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 18 = w64 (rg_s RG) -> getr regs 21 = w64 SHADOW_OFF -> getr regs 22 = w64 SA ->
getr regs 23 = w64 HA ->
4096 <= SA -> SA + 56 <= TT_HI -> rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC -> HA mod 8 = 0 ->
0 <= ei <= 1 -> 0 <= n <= 2 ^ 30 -> 0 <= v < 2 ^ 64 -> 0 <= off < 2 ^ 64 ->
val_mem SEGS (arm W m) (sp + 104) 8 ((rg_s RG + 56) / 8) ->
val_mem SEGS (arm W m) (sp + 112) 8 ((rg_s RG + 48) / 8) ->
val_mem SEGS (arm W m) (sp + 120) 8 ((rg_s RG + 40) / 8) ->
val_mem SEGS (arm W m) (sp + 136) 8 ((rg_s RG + 16) / 8) ->
val_mem SEGS (arm W m) (sp + 144) 8 ((rg_s RG + 32) / 8) ->
val_mem SEGS (arm W m) (sp + 152) 8 ((rg_s RG + 24) / 8) ->
val_mem SEGS (arm W m) (sp + 160) 8 (shadow_addr (SA + 32)) ->
val_mem SEGS (arm W m) (sp + 168) 8 ((rg_s RG + 12) / 8) ->
val_mem SEGS (arm W m) (sp + 176) 8 (shadow_addr SA) ->
val_mem SEGS (arm W m) (HA + 12) 4 ei -> val_mem SEGS (arm W m) (HA + 16) 8 v ->
val_mem SEGS (arm W m) (HA + 24) 4 n -> val_mem SEGS (arm W m) (HA + 32) 8 off ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (tt_extra ei n v off s0 l0 dn))) ss_tt
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_slot)) m (seg_rom SEGS))).
Proof.
intros W regs m sp SA HA ei n v off s0 l0 dn Hsp Hlo Hhi Hal R18 R21 R22 R23 HSA1 HSA2 HHA1 HHA2 HHA8
  Hei Hn Hv Hoff M104 M112 M120 M136 M144 M152 M160 M168 M176 G12 G16 G24 G32.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (GS1 & GS2 & GS3).
unfold ASRC in *. unfold TT_HI in HSA2.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (tt_extra ei n v off s0 l0 dn))).
assert (EREG : forall (k : nat) (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ k r Hr)).
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (tt_extra ei n v off s0 l0 dn) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 SA) by (rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); exact R22).
assert (E23 : ew E 23 = Z_to_bv 64 HA) by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 ei) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 v) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 off) by exact (EX 3%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SB)
  by (rewrite E21, unsigned_lit_small; [reflexivity | unfold SHADOW_OFF; lia]).
assert (U23 : bv_unsigned (ew E 23) = HA) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = ei) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (SR : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 64)
  by (intros x Hx; unfold shadow_addr, SHADOW_OFF;
      assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia); lia).
assert (GR : forall c, 0 <= c < 64 -> 0 <= (rg_s RG + c) / 8 < 2 ^ 64)
  by (intros c Hc; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
unfold ss_tt. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, tt_f1, tt_g0, tt_gs_chunks;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?U23.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 104 8 _ ((rg_s RG + 56) / 8));
        [exact (tt_den_gsh E (rg_s RG) 56 E18 ltac:(lia) ltac:(lia)) | apply GR; lia | zside | exact M104].
    * apply (chunk_ok_val SEGS E _ _ 112 8 _ ((rg_s RG + 48) / 8));
        [exact (tt_den_gsh E (rg_s RG) 48 E18 ltac:(lia) ltac:(lia)) | apply GR; lia | zside | exact M112].
    * apply (chunk_ok_val SEGS E _ _ 120 8 _ ((rg_s RG + 40) / 8));
        [exact (tt_den_gsh E (rg_s RG) 40 E18 ltac:(lia) ltac:(lia)) | apply GR; lia | zside | exact M120].
    * apply (chunk_ok_val SEGS E _ _ 136 8 _ ((rg_s RG + 16) / 8));
        [exact (tt_den_gsh E (rg_s RG) 16 E18 ltac:(lia) ltac:(lia)) | apply GR; lia | zside | exact M136].
    * apply (chunk_ok_val SEGS E _ _ 144 8 _ ((rg_s RG + 32) / 8));
        [exact (tt_den_gsh E (rg_s RG) 32 E18 ltac:(lia) ltac:(lia)) | apply GR; lia | zside | exact M144].
    * apply (chunk_ok_val SEGS E _ _ 152 8 _ ((rg_s RG + 24) / 8));
        [exact (tt_den_gsh E (rg_s RG) 24 E18 ltac:(lia) ltac:(lia)) | apply GR; lia | zside | exact M152].
    * apply (chunk_ok_val SEGS E _ _ 160 8 _ (shadow_addr (SA + 32)));
        [exact (tt_den_shA E 22 SA 32 E22 E21 ltac:(lia) ltac:(lia)) | apply SR; lia | zside | exact M160].
    * apply (chunk_ok_val SEGS E _ _ 168 8 _ ((rg_s RG + 12) / 8));
        [exact (tt_den_gsh E (rg_s RG) 12 E18 ltac:(lia) ltac:(lia)) | apply GR; lia | zside | exact M168].
    * apply (chunk_ok_val SEGS E _ _ 176 8 _ (shadow_addr SA));
        [rewrite (tt_den_shA E 22 SA 0 E22 E21) by lia; rewrite Z.add_0_r; reflexivity
        | apply SR; lia | zside | exact M176].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 12 4 (SOff 32 0) ei); [exact (den_atom0 E 32 ei E32 ltac:(lia)) | zside | zside | exact G12].
    * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 34 0) v); [exact (den_atom0 E 34 v E34 ltac:(lia)) | zside | zside | exact G16].
    * apply (chunk_ok_val SEGS E _ _ 24 4 (SOff 33 0) n); [exact (den_atom0 E 33 n E33 ltac:(lia)) | zside | zside | exact G24].
    * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 35 0) off); [exact (den_atom0 E 35 off E35 ltac:(lia)) | zside | zside | exact G32].
- apply pairwise_disjoint_of_extents. unfold tt_f1, tt_g0, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U23.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [tt_facts0 f_atoms atoms_ok]. unfold afact_ok, tt_IMGF. cbn [af_lo af_hi af_al2].
  rewrite Usp, U18, U21, U23, U32, U33.
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* ---- Bytes read through the ASan view. ---- *)
Lemma tt_garr8_aview : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j H Hj. unfold aview. pose proof (proj2 (H j Hj)) as Hr.
unfold arm in H. rewrite (garr8_mbyte SEGS (mrestrict (w_H W) m) base l j H Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma tt_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.
Lemma tt_garr8_of_aview : forall (W : world SEGS) m a l,
(forall j, (j < length l)%nat -> aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0)) ->
Forall (fun b => 0 <= b < 256) l -> garr8 SEGS (arm W m) a l.
Proof.
intros W m a l H HF j Hj. rewrite Forall_forall in HF.
assert (Hr : 0 <= nth j l 0 < 256) by (apply HF; apply nth_In; exact Hj).
split; [|exact Hr].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte SEGS (w_H W) m (a + Z.of_nat j) _ (H j Hj)) as (b & Hb & Hv & _).
unfold arm. rewrite Hb. rewrite tt_le_byte1 by exact Hr. f_equal. apply bv_eq. rewrite Hv, Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma tt_bzs_range : forall l, Forall (fun b => 0 <= b < 256) (bzs l).
Proof.
intros l. unfold bzs. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (x & <- & _).
unfold bz. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(* ---- Every byte a representation reads lies in its struct or in one of its blocks (W_drain_rest.v rs_). ---- *)
Lemma tt_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.
Lemma tt_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.
Lemma tt_alist_fp_in : forall ly S (W : world SEGS) mem LA l lines,
alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall x, fst r <= x < snd r ->
(LA <= x < LA + 16) \/ exists q m, In (q, m) (alist_blks l) /\ q <= x < q + m.
Proof.
intros ly S W mem LA l lines HL r Hr x Hx.
pose proof HL as (_ & _ & _ & _ & Hnc & Hv & _ & _ & _).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Hx; exact Hx|].
right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []].
  unfold gfp in Hx. cbn [fst snd] in Hx.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (hl_v l), (AREC * hl_cap l). split.
  + unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). left. reflexivity.
  + unfold bzs in Hx. rewrite length_map, length_app, tt_recs_len in Hx. unfold hl_n, AREC in *.
    clear - Hx Hj Hnc. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Hx. cbn [fst snd] in Hx.
  exists (fst q), (Z.of_nat (length (snd q)) + 1). split.
  + unfold alist_blks. apply in_or_app. right. exact (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) _ _ Hq).
  + unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.
Lemma tt_asrc_fp_in : forall ly S (W : world SEGS) mem HA h, asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall x, fst r <= x < snd r ->
(HA <= x < HA + 96) \/ exists q m, In (q, m) (asrc_blks h) /\ q <= x < q + m.
Proof.
intros ly S W mem HA h HS r Hr x Hx.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Hx. unfold ASRC in Hx. lia.
- right. exists (hs_partial h), APARTIAL. split; [left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in Hx. unfold bzs in Hx. rewrite length_map in Hx. lia.
- apply in_app_or in Hr as [Hr | Hr].
  + destruct (tt_alist_fp_in _ _ _ _ _ _ _ Hpend r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
    exists q, m. split; [right; apply in_or_app; left; exact Hq | exact Hqx].
  + apply in_app_or in Hr as [Hr | Hr].
    * destruct (tt_alist_fp_in _ _ _ _ _ _ _ Hexp r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx].
    * destruct (tt_alist_fp_in _ _ _ _ _ _ _ Hheld r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hq | exact Hqx].
Qed.
Local Ltac tt_infp := repeat (first [left; reflexivity | right]).
Lemma tt_aout_fp_in : forall cap out r, In r (aout_fp B RG cap out) -> forall x, fst r <= x < snd r ->
((0x10000 <= x < 0x5fb000) /\ ~ (rg_s RG <= x < rg_s RG + 4 * ASRC) /\
  (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= x < as_errno B + 4))) \/
exists q m, In (q, m) (aout_blks cap out) /\ q <= x < q + m.
Proof.
intros cap out r Hr x Hx.
assert (GD : forall b l, In (b, l) (G_DR B RG) -> b <= x < b + l -> 0x10000 <= x < 0x5fb000).
{ intros b l Hb Hbx. apply pa_img_range. apply (proj1 (HG x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
assert (GO : forall b l, In (b, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] ->
  b <= x < b + l -> 0x10000 <= x < 0x5fb000).
{ intros b l Hb Hbx. apply pa_img_range. apply (proj1 (HGO x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
assert (ZD : forall i k, (i < k)%nat -> (k < 15)%nat -> zdisj (nth i (
  [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
   (rg_s RG, rg_s RG + 4 * ASRC);
   (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
   (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
   (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
   (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
   (as_errno B, as_errno B + 4);
   (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6);
   (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)]) (0, 0)) (nth k (
  [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
   (rg_s RG, rg_s RG + 4 * ASRC);
   (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
   (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
   (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
   (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
   (as_errno B, as_errno B + 4);
   (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6);
   (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)]) (0, 0)))
  by (intros i k Hik Hk; exact (tt_zpw _ i k (0, 0) HRGD Hik ltac:(cbn; lia))).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Hx.
- left. pose proof (ZD 2%nat 7%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 7%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GO (rg_send_max RG) 8); [tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 8%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 8%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GD (rg_nout RG) 8); [unfold G_DR, G_SL; tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 9%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 9%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GD (rg_capout RG) 8); [unfold G_DR, G_SL; tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 10%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 10%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GD (rg_out RG) 8); [unfold G_DR, G_SL; tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 3%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 3%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GO (rg_client RG) 4); [tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 4%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 4%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GD (rg_client_broken RG) 1); [unfold G_DR, G_SL; tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 6%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 6%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GO (rg_send_dead RG) 1); [tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 5%nat ltac:(lia) ltac:(lia)) as D1. pose proof (ZD 5%nat 11%nat ltac:(lia) ltac:(lia)) as D2.
  cbn [nth] in D1, D2. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2.
  split; [apply (GD (rg_send_eintr RG) 1); [unfold G_DR, G_SL; tt_infp | lia]|]. split; [lia | intros _; lia].
- left. pose proof (ZD 2%nat 11%nat ltac:(lia) ltac:(lia)) as D1. cbn [nth] in D1. unfold zdisj in D1. cbn [fst snd] in D1.
  split; [apply (GD (as_errno B) 4); [unfold G_DR, G_SL; tt_infp | lia]|].
  split; [lia | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  right. exists out, cap. split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity | lia].
Qed.
Lemma tt_aentry_fp_in : forall ly S (W : world SEGS) mem e, aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall x, fst r <= x < snd r ->
exists q m, In (q, m) (aentry_blks e) /\ q <= x < q + m.
Proof.
intros ly S W mem e HE r Hr x Hx.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & Huc & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Hx. cbn [fst snd] in Hx. unfold bzs in Hx.
  rewrite length_map, length_app in Hx.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (re_buf e), (re_cap e). split; [|lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Hx. cbn [fst snd] in Hx.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Hx. unfold bzs, key_ptrs in Hx. cbn [map concat length] in Hx. lia.
    * unfold bzs in Hx. rewrite length_map, tt_key_ptrs_len in Hx. unfold re_nheld in Hk1.
      exists (re_hp e), (re_kh e). split; [|lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Hx. cbn [fst snd] in Hx.
    unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
    exists (key_addr k), (Z.of_nat (length (key_text k)) + 1). split; [|lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

(* ---- The round model at the three exits (W_drain_model.v drun_eintr / drun_data). ---- *)
Lemma tt_dlater_eintr : forall cx sg jb a tl,
dlater cx sg jb a tl -> drain_b_c.ds_eintr sg = true -> 4096 <= drain_b_c.ds_cap sg - ulen sg ->
dlater cx (dclr sg) jb a tl.
Proof.
intros cx sg jb a tl (fuel & Hn & Hwf & Ht & Hf) He Hr.
rewrite (dneed_dclr sg He) in Hn.
destruct fuel as [|f]; [lia|].
rewrite (drun_eintr f (dlive cx) (dxmx cx) sg jb a Hr He) in Ht, Hf.
exists f. split; [lia|]. split; [exact Hwf|]. split; [exact Ht | exact Hf].
Qed.

Lemma tt_dpfut0 : forall cx sg jb a tl,
dlater cx sg jb a tl -> drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg <> [] -> dstrict sg ->
4096 <= drain_b_c.ds_cap sg - ulen sg ->
dpfut cx sg 0 jb a (drain_b_c.da_ev a) (drain_b_c.da_erecs a) tl.
Proof.
intros cx sg jb a tl (fuel & Hn & Hwf & Ht & Hf) Hei Hp Hst Hroom.
destruct fuel as [|f]; [unfold dneed in Hn; lia|].
rewrite (drun_data f (dlive cx) (dxmx cx) sg jb a Hroom Hei Hp Hst) in Ht, Hf. cbn [fst snd] in Ht, Hf.
destruct (dneed_dnext (dlive cx) (dxmx cx) sg Hroom Hp Hwf Hst Hei) as (Hn' & Hwf').
unfold dpfut. cbv zeta.
change (Z.of_nat (length (lines (drain_b_c.ds_ref sg) (firstn 0 (ddata sg))))) with 0. rewrite Z.add_0_r.
assert (Epu : drain_b_c.pushes_run (drain_b_c.ds_en sg)
  (pcapm (drain_b_c.ds_en sg) (drain_b_c.ds_ecap sg) (lines (drain_b_c.ds_ref sg) (firstn 0 (ddata sg))))
  (lines (feed (drain_b_c.ds_ref sg) (firstn 0 (ddata sg))) (skipn 0 (ddata sg))) jb
  (drain_b_c.da_ev a) (drain_b_c.da_erecs a) = dpush sg jb a) by reflexivity.
rewrite Epu. clear Epu.
exists (ddrop sg a ++ fst (fst (dlines (dlive cx) (dxmx cx) sg jb a)) ++
  fst (drain_b_c.drain_run f (dlive cx) (dxmx cx) (dnext (dlive cx) (dxmx cx) sg)
    (jb + dnret (fst (fst (dpush sg jb a))) + dnret (ddrop sg a) + dnret (fst (fst (dlines (dlive cx) (dxmx cx) sg jb a))))
    (dnext_a (dlive cx) (dxmx cx) sg jb a))).
split; [|exact (eq_sym Ht)].
unfold drfut.
exists (fst (fst (dlines (dlive cx) (dxmx cx) sg jb a)) ++
  fst (drain_b_c.drain_run f (dlive cx) (dxmx cx) (dnext (dlive cx) (dxmx cx) sg)
    (jb + dnret (fst (fst (dpush sg jb a))) + dnret (ddrop sg a) + dnret (fst (fst (dlines (dlive cx) (dxmx cx) sg jb a))))
    (dnext_a (dlive cx) (dxmx cx) sg jb a))).
split; [|reflexivity].
unfold dlfut. cbv zeta.
exists (fst (drain_b_c.drain_run f (dlive cx) (dxmx cx) (dnext (dlive cx) (dxmx cx) sg)
    (jb + dnret (fst (fst (dpush sg jb a))) + dnret (ddrop sg a) + dnret (fst (fst (dlines (dlive cx) (dxmx cx) sg jb a))))
    (dnext_a (dlive cx) (dxmx cx) sg jb a))).
split; [|reflexivity].
exists f. split; [lia|]. split; [exact Hwf'|].
assert (Ea : danext (if dwhole sg then drain_b_c.DA (drain_b_c.da_out (dapush a (snd (dpush sg jb a))))
    (drain_b_c.da_buf (dapush a (snd (dpush sg jb a)))) (drain_b_c.da_hp (dapush a (snd (dpush sg jb a))))
    (drain_b_c.da_keys (dapush a (snd (dpush sg jb a))))
    (skipn 1 (drain_b_c.da_pend (dapush a (snd (dpush sg jb a)))))
    (drain_b_c.da_ev (dapush a (snd (dpush sg jb a)))) (drain_b_c.da_erecs (dapush a (snd (dpush sg jb a))))
    else dapush a (snd (dpush sg jb a))) (snd (dlines (dlive cx) (dxmx cx) sg jb a)) =
  dnext_a (dlive cx) (dxmx cx) sg jb a).
{ unfold danext, dnext_a, dapush. destruct (dwhole sg); reflexivity. }
split.
- match goal with |- fst (drain_b_c.drain_run _ _ _ _ _ ?A) = _ =>
    replace A with (dnext_a (dlive cx) (dxmx cx) sg jb a) by exact (eq_sym Ea) end. reflexivity.
- match goal with |- fst (snd (drain_b_c.drain_run _ _ _ _ _ ?A)) = _ =>
    replace A with (dnext_a (dlive cx) (dxmx cx) sg jb a) by exact (eq_sym Ea) end. exact Hf.
Qed.

(* ---- The memory core after the EINTR round: g_s[j].eintr = 0, errno = EINTR, all else kept. ---- *)
Lemma tt_abyte_trans : forall (W1 W2 W3 : world SEGS) m1 m2 m3 x,
abyte_kept W1 m1 W2 m2 x -> abyte_kept W2 m2 W3 m3 x -> abyte_kept W1 m1 W3 m3 x.
Proof. intros W1 W2 W3 m1 m2 m3 x [A1 B1] [A2 B2]. split; [rewrite A2; exact A1 | intros H; exact (B2 (B1 H))]. Qed.

Lemma tt_errno_sep : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (tt_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (tt_zpw _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (tt_zpw _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (tt_zpw _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (tt_zpw _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (tt_zpw _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (tt_zpw _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (tt_zpw _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (tt_zpw _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

(* W_drain_epi.v dend_aout_ev: the controller's cells with a new errno value *)
Lemma tt_aout_ev : forall ly S (W : world SEGS) m m' c O mx no cap out ev,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W m W m' a) ->
(cap <> 0 -> forall a, out <= a < out + cap -> ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W m') (as_errno B) 4 ev -> awr W m' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
aout_at B RG ly S W m' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev) O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out ev
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HOB VE WE Hev.
assert (KC : forall a n, In (a, a + n) (aout_fp B RG cap out) -> forall x, a <= x < a + n ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W m W m' x)
  by (intros a n Hin x Hx Hne; exact (HK (a, a + n) Hin x Hx Hne)).
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H1]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H2]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H3]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H4]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H5]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H6]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H7]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H8]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H9]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H10]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H11]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H12]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H13]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H14]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H15]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; tt_infp | lia | apply tt_errno_sep; repeat (first [left; lia | right]); lia] | exact H16]|].
split; [exact VE|]. split; [exact WE|]. split; [exact Hev|].
do 6 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W m); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold aout_fp; rewrite Ec; tt_infp | lia | apply (HOB ltac:(lia)); lia].
Qed.

Lemma tt_asrc_clr : forall ly S (W : world SEGS) m m' HA h,
asrc_at B ly S W m HA h ->
(forall x, HA <= x < HA + 96 -> ~ (HA + 12 <= x < HA + 16) -> abyte_kept W m W m' x) ->
(forall q n x, In (q, n) (asrc_blks h) -> q <= x < q + n -> abyte_kept W m W m' x) ->
(forall x, writable_at SEGS (arm W m) x -> writable_at SEGS (arm W m') x) ->
val_mem SEGS (arm W m') (HA + 12) 4 0 ->
asrc_at B ly S W m' HA (tt_clr_ei h).
Proof.
intros ly S W m m' HA h
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
   H21 & H22 & H23 & H24) KS KB KW V12.
assert (Hvm : forall a n v, HA <= a -> a + Z.of_nat n <= HA + 96 -> ~ (a < HA + 16 /\ HA + 12 < a + Z.of_nat n) ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v)
  by (intros a n v Ha Hn Hno Hv; apply (akept_vm W m); [intros x Hx; apply KS; lia | exact Hv]).
assert (HL : forall LA l lines, HA + 16 <= LA -> LA + 16 <= HA + 96 ->
  (forall b, In b (alist_blks l) -> In b (asrc_blks h)) ->
  alist_at B ly S W m LA l lines -> alist_at B ly S W m' LA l lines).
{ intros LA l lines H1a H2a Hsub HLA. apply (alist_at_kept B ly S W m); [exact HLA | |].
  - intros r Hr x Hx. destruct (tt_alist_fp_in _ _ _ _ _ _ _ HLA r Hr x Hx) as [X | (q & n & Hq & Hqx)].
    + apply KS; lia.
    + exact (KB q n x (Hsub _ Hq) Hqx).
  - exact (tt_alist_blks_in ly S W m LA l lines HLA). }
unfold asrc_at, tt_clr_ei. cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial
  hs_overlong hs_pad hs_expected hs_held].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H3]|].
split; [exact V12|].
split; [intros i Hi; apply KW; exact (H5 i Hi)|].
split; [exact H6|]. split; [left; reflexivity|]. split; [exact H8|]. split; [exact H9|].
split; [apply (HL (HA + 16)); [lia | lia | intros b Hb; right; apply in_or_app; left; exact Hb | exact H10]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|]. split; [exact H18|]. split; [exact H19|].
split; [apply (akept_garr8 W m); [intros x Hx; apply (KB (hs_partial h) APARTIAL x); [left; reflexivity|];
  unfold bzs in Hx; rewrite length_map in Hx; lia | exact H20]|].
split; [exact H21|].
split; [apply (HL (HA + 64)); [lia | lia | intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb
  | exact H22]|].
split; [apply (HL (HA + 80)); [lia | lia | intros b Hb; right; apply in_or_app; right; apply in_or_app; right; exact Hb
  | exact H23]|].
exact H24.
Qed.

(* the entry's 56 bytes *)
Lemma tt_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (bzs (entry_bytes e)) = 56%nat.
Proof.
intros e H1 H2. rewrite tt_bzs_len. unfold entry_bytes.
rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.

Lemma tt_dmem_eintr : forall cx sg ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) -> ~ (as_errno B <= x < as_errno B + 4) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
val_mem SEGS (arm W1 mF) (dHA RG cx + 12) 4 0 ->
val_mem SEGS (arm W1 mF) (as_errno B) 4 4 ->
DMEM B RG cx ly1 S1 W1 mF mdF k1 e1 (tt_clr_ei h1) (dclr sg) out1 4 sent LB1.
Proof.
intros cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF HB HMEM HJF KEEP PRES V12 VERR.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx)
  by (unfold dsp0; clear - Hslo Hceil; change DRAIN_STK with 16848 in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
pose proof HGSB as (GS1 & GS2 & GS3).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; clear - Hj4; lia).
assert (GIMG : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GSG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (ERG : forall x, as_errno B <= x < as_errno B + 4 -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]).
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
{ pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B) ltac:(lia)))) as P0.
  pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B + 3) ltac:(lia)))) as P3. lia. }
pose proof tt_errno_gs as TEG.
assert (KB : forall x, 0 <= x < alloc_ceiling -> ~ in_img SEGS x -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx Hni. split.
  - apply KEEP; [clear - Hx C1; lia | intros Hy; apply Hni, GIMG, GSG; clear - Hy HAr; lia
    | intros Hy; apply Hni, GIMG, ERG; exact Hy | clear - Hx HspA; unfold ESTACK, DRAIN_FRAME; lia].
  - unfold arm. apply writable_kept. apply PRES. }
assert (KI : forall x, 0x10000 <= x < 0x5fb000 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx N1 N2. split.
  - apply KEEP; [lia | exact N1 | exact N2 | clear - Hx HspA C1; unfold ESTACK, DRAIN_FRAME; lia].
  - unfold arm. apply writable_kept. apply PRES. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. split.
  - apply KEEP; [clear - Hx HspA HspB C1; unfold DRAIN_FRAME in *; lia
    | clear - Hx HspA HAr GS2 C1; unfold DRAIN_FRAME, ASRC in *; lia
    | clear - Hx HspA HERRI C1; unfold DRAIN_FRAME in *; lia | lia].
  - unfold arm. apply writable_kept. apply PRES. }
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> q <= x < q + n -> abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof (tt_req_ge n) as Rq. apply KB; [clear - Hx H4 Hc Rq; lia|].
  apply (tt_blk_noimg _ _ _ _ _ q n x HAR Hin). clear - Hx Rq. lia. }
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept _ m1 mF x (PRES x) Hw)).
pose proof HEOK as (_ & _ & Hpad1 & Hpad2 & _).
split; [exact HJF|].
split.
{ intros x Hx. pose proof (pa_img_range _ (tt_rom_img x Hx)) as Hxr. rewrite KEEP; [exact (Hrom x Hx) | lia
  | intros Hy; apply (HGR x); [apply GSG; clear - Hy HAr; lia | exact Hx]
  | intros Hy; apply (HGR x); [apply ERG; exact Hy | exact Hx]
  | clear - Hxr HspA C1; unfold ESTACK, DRAIN_FRAME; lia]. }
split; [intros a Ha1 Ha2 Ha3 Ha4; apply PRES; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & ASV).
  assert (HVM : forall o n v, 0 <= o -> o + Z.of_nat n <= DRAIN_FRAME ->
    val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o) n v -> val_mem SEGS (arm W1 mF) (dsp0 cx - DRAIN_FRAME + o) n v)
    by (intros o n v Ho Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply KFR; lia | exact Hv]).
  repeat match goal with |- _ /\ _ => split end;
    try (apply HVM; [lia | cbn; unfold DRAIN_FRAME; lia | assumption]).
  intros i Hi. specialize (ASV i Hi).
  replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i))
    in ASV |- * by lia.
  apply HVM; [lia | cbn; unfold DRAIN_FRAME; lia | exact ASV]. }
split.
{ apply (tt_garr8_kept W1 m1 W1 mF _ _ Hgarr). intros x Hx. rewrite (tt_entry_len e1 Hpad1 Hpad2) in Hx.
  apply (proj1 (KBL (dxG cx) ATABLE x HGin1 ltac:(clear - Hx HGSA HSAG; unfold AENT, ATABLE in *; lia))). }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ apply (tt_aentry_okx_kept ly1 S1 W1 m1 ly1 S1 W1 mF e1 HEOK); [|exact (tt_aentry_blks_in ly1 S1 W1 m1 e1 HEOK)].
  intros r Hr x Hx. destruct (tt_aentry_fp_in _ _ _ _ _ HEOK r Hr x Hx) as (q & n & Hq & Hqx).
  exact (KBL q n x (tt_aentry_blks_in _ _ _ _ _ HEOK _ Hq) Hqx). }
split.
{ apply (tt_asrc_clr ly1 S1 W1 m1 mF (dHA RG cx) h1 Hsrc).
  - intros x Hx N. apply KI; [clear - Hx HAr GS1 GS2; unfold ASRC in *; lia | exact N
    | intros Hy; clear - Hy Hx HAr TEG; unfold ASRC in *; lia].
  - intros q n x Hq Hqx. exact (KBL q n x (tt_asrc_blks_in _ _ _ _ _ _ Hsrc _ Hq) Hqx).
  - exact HWK.
  - exact V12. }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KI;
      clear - Hx Hi Hne Hj4 GS1 GS2 TEG; unfold dHA, ASRC in *; lia.
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KI;
      clear - Hx Hi Hne Hj4 GS1 GS2 TEG; unfold dHA, ASRC in *; lia. }
split.
{ intros x Hx1 Hx2. apply (tt_abyte_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2)).
  apply KI; [clear - Hx1 GS1 GS2; unfold ASRC in *; lia | intros Hy; apply Hx2; clear - Hy; unfold ASRC; lia
  | intros Hy; clear - Hy Hx1 TEG; lia]. }
split.
{ pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AWERR & _).
  refine (tt_aout_ev ly1 S1 W1 m1 mF _ _ _ _ _ _ 4 Hout _ _ VERR _ _).
  - intros r Hr x Hx Hne. destruct (tt_aout_fp_in _ _ r Hr x Hx) as [(Hi1 & Hi2 & _) | (q & n & Hq & Hqx)].
    + apply KI; [exact Hi1 | intros Hy; apply Hi2; clear - Hy HAr; lia | exact Hne].
    + exact (KBL q n x (tt_aout_blks_in _ _ _ _ _ _ _ _ _ _ Hout _ Hq) Hqx).
  - intros Hc x Hx Hy.
    assert (Hin : In (out1, drain_b_c.ds_ocap sg) (ablocks B ly1 S1)).
    { apply (tt_aout_blks_in _ _ _ _ _ _ _ _ _ _ Hout). unfold aout_blks.
      rewrite (proj2 (Z.eqb_neq _ 0) Hc). left. reflexivity. }
    apply (tt_blk_noimg _ _ _ _ _ _ _ x HAR Hin); [pose proof (tt_req_ge (drain_b_c.ds_ocap sg)); lia|].
    apply GIMG, ERG. exact Hy.
  - intros i Hi. apply HWK. exact (AWERR i Hi).
  - lia. }
split; [exact Hlivout | exact Hperm].
Qed.

(* ---- The memory core after the data round's copy: the relay's buffer holds the n bytes after s->used. ---- *)
Lemma tt_skipn_bzs : forall k l, skipn k (bzs l) = bzs (skipn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. apply IH. Qed.
Lemma tt_firstn_bzs : forall k l, firstn k (bzs l) = bzs (firstn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma tt_garr8_skipn : forall m a l k, garr8 SEGS m a l -> (k <= length l)%nat ->
garr8 SEGS m (a + Z.of_nat k) (skipn k l).
Proof.
intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply garr8_app in H as [_ H].
rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Lemma tt_dmem_drb : forall cx sg ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF (data : list byte),
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
0 < re_cap e1 -> (length data <= length (re_junk e1))%nat ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
   ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
   ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
(forall i, (i < length data)%nat ->
   aview SEGS (w_H W1) mF (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)) ->
DMEM B RG cx ly1 S1 W1 mF mdF k1 (tt_junk e1 (data ++ skipn (length data) (re_junk e1))) h1 sg out1 ev1 sent LB1.
Proof.
intros cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF data HB HMEM HJF Hcp Hdl KEEP PRES CPY.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx)
  by (unfold dsp0; clear - Hslo Hceil; change DRAIN_STK with 16848 in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
pose proof HGSB as (GS1 & GS2 & GS3).
pose proof HEOK as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
  HND1 & HND2 & Hkeys).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [clear - Hc0 Hcp; lia|].
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & _). rewrite RQC in Hbceil.
assert (Hboff : off_img (re_buf e1) (re_cap e1))
  by (pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR Hbin) as X; rewrite RQC in X; exact X).
pose proof (Permutation_NoDup Hperm (tt_ablocks_nodup _ _ _ _ _ HAR)) as HNDp.
unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by lia. cbn [app] in HNDp.
apply List.NoDup_cons_iff in HNDp as [HGnot HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot _].
assert (HDL : Z.of_nat (length data) <= re_cap e1 - re_used e1) by (rewrite <- Hjl; lia).
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> (q, n) <> (re_buf e1, re_cap e1) -> q <= x < q + n ->
  abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hne Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof (tt_req_ge n) as Rq.
  pose proof (tt_blk_apart _ _ _ _ _ _ _ _ _ HAR Hin Hbin Hne) as Hap. rewrite RQC in Hap.
  split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; clear - Hx H4 Hc Rq Hap HspA C1 HUlen HDL; unfold tt_apart, DRAIN_FRAME, ESTACK in *; lia. }
assert (KI : forall x, 0x10000 <= x < 0x5fb000 -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; clear - Hx HspA C1 Hboff HUlen HDL; unfold off_img, DRAIN_FRAME, ESTACK in *; lia. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME + 88 <= x < dsp0 cx - DRAIN_FRAME + 192 \/
  dsp0 cx - DRAIN_FRAME + 208 <= x < dsp0 cx -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; clear - Hx HspA HspB C1 Hbceil HUlen HDL; unfold DRAIN_FRAME, ESTACK in *; lia. }
assert (NB : forall b, In b (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> b <> (re_buf e1, re_cap e1))
  by (intros b Hb Heq; apply Hbufnot; rewrite <- Heq; exact Hb).
assert (INB : forall b, In b (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). right. unfold aentry_blks.
  rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by lia. cbn [app]. right. exact Hb. }
assert (KH : forall q n x, In (q, n) (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> q <= x < q + n ->
    abyte_kept W1 m1 W1 mF x)
  by (intros q n x Hb Hx; exact (KBL q n x (INB _ Hb) (NB _ Hb) Hx)).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept _ m1 mF x (PRES x) Hw)).
split; [exact HJF|].
split; [intros x Hx; pose proof (pa_img_range _ (tt_rom_img x Hx)) as Hxr; rewrite (proj1 (KI x Hxr));
  exact (Hrom x Hx)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply PRES; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & ASV).
  assert (HVM : forall o n v, 88 <= o -> (o + Z.of_nat n <= 192 \/ 208 <= o) -> o + Z.of_nat n <= DRAIN_FRAME ->
    val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o) n v -> val_mem SEGS (arm W1 mF) (dsp0 cx - DRAIN_FRAME + o) n v)
    by (intros o n v Ho1 Ho2 Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply KFR; lia | exact Hv]).
  repeat match goal with |- _ /\ _ => split end;
    try (apply HVM; [lia | cbn; lia | cbn; unfold DRAIN_FRAME; lia | assumption]).
  intros i Hi. specialize (ASV i Hi).
  replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i))
    in ASV |- * by lia.
  apply HVM; [lia | cbn; lia | cbn; unfold DRAIN_FRAME; lia | exact ASV]. }
split.
{ assert (G0 : garr8 SEGS (arm W1 mF) (dxSA cx) (bzs (entry_bytes e1))).
  { apply (tt_garr8_kept W1 m1 W1 mF _ _ Hgarr). intros x Hx. rewrite (tt_entry_len e1 Hpad1 Hpad2) in Hx.
    apply (proj1 (KBL (dxG cx) ATABLE x HGin1
      ltac:(intros X; injection X as X1 X2; clear - X2 Hcapr Hcp; unfold ATABLE in *; lia)
      ltac:(clear - Hx HGSA HSAG; unfold AENT, ATABLE in *; lia))). }
  exact G0. }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ unfold aentry_okx, tt_junk.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
  split; [exact Heof|]. split; [exact Hskip|]. split; [exact Hpad1|]. split; [exact Hpad2|].
  split; [exact Hfd|]. split; [exact Hcapr|]. split; [exact HUlen|]. split; [exact Husedc|].
  split.
  { right. split; [exact Hcpos|]. split; [exact Hbin|].
    split; [rewrite length_app, length_skipn; clear - Hjl Hdl; lia|].
    rewrite tt_bzs_app in Hbuf8. apply garr8_app in Hbuf8 as [GU GJ].
    rewrite !tt_bzs_app. apply garr8_app. split.
    - apply (tt_garr8_kept W1 m1 W1 mF _ _ GU). intros x Hx. rewrite tt_bzs_len in Hx.
      apply KEEP; clear - Hx HUlen HDL Hbceil Hb4096 HspA C1; unfold DRAIN_FRAME, ESTACK in *; lia.
    - rewrite tt_bzs_len. rewrite HUlen. apply garr8_app. split.
      + apply tt_garr8_of_aview; [|apply tt_bzs_range].
        intros i Hi. rewrite tt_bzs_len in Hi. exact (CPY i Hi).
      + rewrite tt_bzs_len, HUlen in GJ.
        pose proof (tt_garr8_skipn _ _ _ (length data) GJ ltac:(rewrite tt_bzs_len; exact Hdl)) as GJ'.
        rewrite tt_skipn_bzs in GJ'. rewrite tt_bzs_len.
        apply (tt_garr8_kept W1 m1 W1 mF _ _ GJ'). intros x Hx. rewrite tt_bzs_len, length_skipn in Hx.
        apply KEEP; clear - Hx HUlen HDL Hbceil Hb4096 HspA C1 Hjl Hdl; unfold DRAIN_FRAME, ESTACK in *; lia. }
  split; [exact Hnheld|].
  split.
  { destruct Hheld as [H0 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H0 | right].
    split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx.
    apply (KH (re_hp e1) (re_kh e1)); [apply in_or_app; left; apply in_or_app; left;
      rewrite (proj2 (Z.eqb_neq _ 0) Hz); left; reflexivity|].
    unfold bzs in Hx. rewrite length_map, tt_key_ptrs_len in Hx. unfold re_nheld in Hk1. lia. }
  split; [exact HND1|]. split; [exact HND2|].
  rewrite Forall_forall in Hkeys |- *. intros k Hk. destruct (Hkeys k Hk) as (K1 & K2 & K3).
  split; [exact K1|]. split; [|exact K3].
  apply (akept_garr8 W1 m1); [|exact K2]. intros x Hx.
  apply (KH (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
  - apply in_or_app. left. apply in_or_app. right.
    exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hk).
  - unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia. }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 mF (dHA RG cx) h1 Hsrc); [|exact (tt_asrc_blks_in _ _ _ _ _ _ Hsrc)].
  intros r Hr x Hx. destruct (tt_asrc_fp_in _ _ _ _ _ _ Hsrc r Hr x Hx) as [X | (q & n & Hq & Hqx)].
  - apply KI. clear - X Hj4 GS1 GS2. unfold dHA, ASRC in *. lia.
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. left. exact Hq. }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KI.
    clear - Hx Hi GS1 GS2. unfold ASRC in *. lia.
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KI.
    clear - Hx Hi GS1 GS2. unfold ASRC in *. lia. }
split.
{ intros x Hx1 Hx2. apply (tt_abyte_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2)).
  apply KI. clear - Hx1 GS1 GS2. unfold ASRC in *. lia. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF); [exact Hout | |
    exact (tt_aout_blks_in _ _ _ _ _ _ _ _ _ _ Hout)].
  intros r Hr x Hx. destruct (tt_aout_fp_in _ _ r Hr x Hx) as [(Hi1 & _) | (q & n & Hq & Hqx)].
  - exact (KI x Hi1).
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hq. }
split; [exact Hlivout | exact Hperm].
Qed.

(* ---- The bytes the data round copies: [off, off + n) of the head pending text. ---- *)
Lemma tt_nth_firstn : forall {A} k (l : list A) i d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
intros A k. induction k as [|k IH]; intros l i d H; [lia|].
destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma tt_nth_skipn : forall {A} o (l : list A) i d, nth i (skipn o l) d = nth (o + i) l d.
Proof.
intros A o. induction o as [|o IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [rewrite skipn_nil; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma tt_nth_data : forall (t : list byte) (z : byte) (o k i : nat), (o + k <= length t)%nat -> (i < k)%nat ->
nth (o + i) (bzs (t ++ [z])) 0 = nth i (bzs (firstn k (skipn o t))) 0.
Proof.
intros t z o k i Hl Hi. rewrite <- tt_firstn_bzs, <- tt_skipn_bzs, tt_nth_firstn by exact Hi.
rewrite tt_nth_skipn, tt_bzs_app. apply app_nth1. rewrite tt_bzs_len. lia.
Qed.

(* a side goal between numerals, decided by computation: lia would scan (and case-split) the whole context *)
Ltac tt_num := repeat match goal with |- _ /\ _ => split end;
  first [ reflexivity | apply Nat.ltb_lt; vm_compute; reflexivity | apply Nat.leb_le; vm_compute; reflexivity
        | apply Z.ltb_lt; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity ].

(* the write obligation of a run whose windows are read-only or drain's own frame slots *)
Ltac tt_awr_regions Usp HDS :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_x_nil
  | apply awr_ok_x_cons; [intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia|]
  | apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
      left; split; [left; rewrite HDS; unfold DRAIN_FRAME in *; clear - Ha; lia | clear - Ha; lia] |] ].

Theorem dr_toptail : dr_toptail_stmt B MT MMAX RG.
Proof.
unfold dr_toptail_stmt. intros cx sg D W1 c1 HB HT2 Kdi Kend Krb.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HT2 as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24 & R10 & R13 &
  HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
pose proof HFR as HFR'. unfold dr_frame in HFR'. cbv zeta in HFR'.
destruct HFR' as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSA0 & HGin0 & HGSA & HSAG & _ & _ & _ & Hj4 & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
pose proof Hafn as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
fold (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16848) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx) by (clear - Hslo Hceil HDS; rewrite HDS in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HGin1) as (_ & HG4096 & HGceil & HGapp & _).
rewrite RQT in HGceil, HGapp.
pose proof HGSB as (GS1 & GS2 & GS3).
set (j := dxj cx) in *. set (GS := rg_s RG) in *. set (SA := dxSA cx) in *.
assert (HHA : dHA RG cx = GS + 96 * Z.of_nat j) by (unfold dHA, ASRC; reflexivity).
pose proof Hsrc as (V0 & V4 & V8 & V12 & HAWS & Hcl01 & Hei01 & Hopen & Hfdr & HPEND & V32 & V40 & V48 & V56 &
  Hrecs & Hnpart & Hovl & Hpin & Hpjl & Hpg & HnoW & HEXP & HHELD & HNDB).
pose proof HPEND as (P0 & P8 & P12 & PAW & Pn & Pv & PND & Pnv & Precs).
rewrite HHA in R23, V0, V4, V8, V12, HAWS, V32, V40, V48, V56, P0, P8, P12, PAW.
replace (dHA RG cx) with (GS + 96 * Z.of_nat j) in * by (symmetry; exact HHA).
replace (GS + 96 * Z.of_nat j + 16 + 8) with (GS + 96 * Z.of_nat j + 24) in P8 by lia.
replace (GS + 96 * Z.of_nat j + 16 + 12) with (GS + 96 * Z.of_nat j + 28) in P12 by lia.
set (HA := GS + 96 * Z.of_nat j) in *.
set (ei := hs_eintr h1) in *. set (nn := hl_n (hs_pending h1)) in *. set (vv := hl_v (hs_pending h1)) in *.
set (off := hs_off h1) in *.
set (s0 := fst (tt_hd (hs_pending h1))). set (l0 := Z.of_nat (length (snd (tt_hd (hs_pending h1))))).
set (dn := dnum sg).
assert (Hj4' : 0 <= Z.of_nat j < 4) by lia.
assert (Hnn : 0 <= nn <= 2 ^ 30) by (unfold nn, hl_n in *; lia).
assert (Hvv : 0 <= vv < 2 ^ 64).
{ destruct Pv as [(_ & Hv0) | (Hcp & Hin & _)]; [rewrite Hv0; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof (tt_req_ge (AREC * hl_cap (hs_pending h1))). unfold AREC in *. lia. }
assert (Hoff : 0 <= off < 2 ^ 64).
{ destruct Hrecs as [(_ & ->) | (r & rs & Er & Ho1 & Ho2)]; [lia|].
  rewrite Forall_forall in Precs. destruct (Precs r ltac:(rewrite Er; left; reflexivity)) as (Hin & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _). pose proof (tt_req_ge (Z.of_nat (length (snd r)) + 1)). lia. }
pose proof (tt_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) SA HA ei nn vv off s0 l0 dn Hsp
  ltac:(unfold DRAIN_FRAME; lia) ltac:(unfold DRAIN_FRAME; lia) ltac:(unfold DRAIN_FRAME; rewrite Zminus_mod, Hal16; reflexivity)
  R18 R21 R22 R23 ltac:(unfold AENT, ATABLE in *; lia) ltac:(unfold TT_HI, AENT, ATABLE in *; lia)
  ltac:(unfold HA; lia) ltac:(unfold HA, ASRC in *; lia) ltac:(unfold HA; rewrite Z.add_mod, GS3 by lia;
    replace (96 * Z.of_nat j) with ((12 * Z.of_nat j) * 8) by lia; rewrite Z.mod_mul by lia; reflexivity)
  ltac:(unfold ei in *; lia) Hnn Hvv Hoff F104 F112 F120 F136 F144 F152 F160 F168 F176 V12 P0 P8 V32) as HS.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
remember (Eimg (Ereg regs1 (tt_extra ei nn vv off s0 l0 dn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (k : nat) (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ k r Hr)).
assert (EX : forall i, (i < 7)%nat -> ew E (32 + i) = nth i (tt_extra ei nn vv off s0 l0 dn) (Z_to_bv 64 0))
  by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
assert (E18 : ew E 18 = Z_to_bv 64 GS) by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 SA) by (rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); exact R22).
assert (E23 : ew E 23 = Z_to_bv 64 HA) by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat j))
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (E32 : ew E 32 = Z_to_bv 64 ei) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 nn) by exact (EX 1%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (HAr : GS <= HA /\ HA + 96 <= GS + 4 * ASRC) by (unfold HA, ASRC; clear - Hj4'; lia).
assert (SHOK : sh_ok SEGS (SOff 21 0) TT_SH0 E (mrestrict (w_H W1) m1)).
{ unfold sh_ok, TT_SH0. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E (SOff 21 0) 23 GS (4 * ASRC) HA 0 96).
  - exact (azs_range_addressable B LAWS ly1 S1 W1 m1 md1 GS (4 * ASRC) HAR HGSZ).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - apply (U_atom E 23 HA E23). unfold ASRC in *. lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF, ASRC in *. lia. }
(* ---- 0x83314 .. 0x8331c: the shadow address of &g_s[j].eintr, re-expressed ---- *)
paj_run_to_tok RUNTO HS HJ SHOK TTspan A_tt_sh1. { apply awr_ok_x_of0. awr_ok_tac. }
rename HFr into FR1; rename HG0 into GR1; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msA end.
tt_reg HS (14%bv : bv 5) X14.
assert (D14 : getr (ms_regs (restrict (w_H W1) msA)) 14%bv = sv_denot E (tt_shA 23 12)).
{ cbn [ms_regs restrict]. rewrite X14. apply (tt_den_resh E GS (Z.of_nat j) 12 E18 E24 E23 E21); unfold ASRC in *; lia. }
pose proof (tt_reseat E _ _ 14%bv _ HS D14 eq_refl) as HS'. clear HS D14 X14. rename HS' into HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
(* ---- 0x8331c .. 0x8332c: the shadow check folds; the test of g_s[j].eintr ---- *)
paj_run_tok RUN HS HJ SHOK TTspan. { apply awr_ok_x_of0. awr_ok_tac. }
rename HFr into FR2; rename HG0 into GR2; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
(* the two runs store nothing: every view kept, presence grown *)
assert (KALL2 : forall x, aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) m1 x).
{ intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msA) (ms_mem msB) x)
    by (apply FR2; apply tt_nowr; vm_compute; reflexivity).
  apply (aview_eq_of SEGS (w_H W1) m1 (ms_mem msA) x). apply FR1; apply tt_nowr; vm_compute; reflexivity. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msB) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hp))).
assert (U23 : bv_unsigned (ew E 23) = HA) by (rewrite E23; apply unsigned_lit_small; unfold ASRC in *; lia).
psrr_branch_tok RUN BR HS SHOK TTspan.
- (* g_s[j].eintr == 0: the empty-pending test *)
  rewrite branch_eq_U, (U_atom E 32 ei E32), (U_lit E 0) in Hc by (unfold ei in *; lia).
  apply Z.eqb_eq in Hc. rename Hc into Hei0.
  paj_run_to_tok RUNTO HS HJ SHOK TTspan A_tt_sh2. { apply awr_ok_x_of0. awr_ok_tac. }
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msC end.
  tt_reg HS (15%bv : bv 5) X15.
  assert (D15 : getr (ms_regs (restrict (w_H W1) msC)) 15%bv = sv_denot E (tt_shA 23 24)).
  { cbn [ms_regs restrict]. rewrite X15. apply (tt_den_resh E GS (Z.of_nat j) 24 E18 E24 E23 E21); unfold ASRC in *; lia. }
  pose proof (tt_reseat E _ _ 15%bv _ HS D15 eq_refl) as HS'. clear HS D15 X15. rename HS' into HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
  (* ---- 0x8336c .. 0x8337c: the shadow check folds; the test of g_s[j].pending.n ---- *)
  paj_run_tok RUN HS HJ SHOK TTspan. { apply awr_ok_x_of0. awr_ok_tac. }
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msD end.
  assert (KALL4 : forall x, aview SEGS (w_H W1) (ms_mem msD) x = aview SEGS (w_H W1) m1 x).
  { intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msC) (ms_mem msD) x)
      by (apply FR4; apply tt_nowr; vm_compute; reflexivity).
    rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msB) (ms_mem msC) x)
      by (apply FR3; apply tt_nowr; vm_compute; reflexivity).
    exact (KALL2 x). }
  assert (PRES4 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msD) x)
    by (intros x Hp; exact (apresent_grows _ _ _ _ GR4 (apresent_grows _ _ _ _ GR3 (PRES2 x Hp)))).
  psrr_branch_tok RUN BR HS SHOK TTspan.
  + (* g_s[j].pending.n == 0: DEND *)
    rewrite branch_eq_U, (U_atom E 33 nn E33), (U_lit E 0) in Hc by lia.
    apply Z.eqb_eq in Hc. rename Hc into Hn0.
    paj_run_to_tok RUNTO HS HJ SHOK TTspan A_dr_end. { apply awr_ok_x_of0. awr_ok_tac. }
    rename HFr into FR5; rename HG0 into GR5; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
    assert (KALLF : forall x, aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
    { intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msD) (ms_mem msF) x)
        by (apply FR5; apply tt_nowr; vm_compute; reflexivity).
      exact (KALL4 x). }
    assert (PRESF : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR5 (PRES4 x Hp))).
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
    prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
    pose proof (tt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem msF) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KALLF PRESF) as HMEMF.
    pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
    match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
    apply (Kend W1). unfold DEND.
    exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [unfold cfg_at; reflexivity|].
    split; [unfold spZ; rewrite P2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite P3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite P4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite P22, E22; reflexivity|].
    split; [rewrite P18, E18; reflexivity|].
    split; [rewrite P21, E21; reflexivity|].
    split; [rewrite P23, E23; reflexivity|].
    split; [rewrite P24, E24; reflexivity|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 HMEMF)))))|].
    split; [exact HMEMF|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|].
    split.
    { rewrite <- Lpend. unfold nn, hl_n in Hn0. destruct (hl_recs (hs_pending h1)); [reflexivity | cbn in Hn0; lia]. }
    split; [unfold ei in Hei0; rewrite Hei0 in Lei; destruct (drain_b_c.ds_eintr sg); [discriminate | reflexivity]|].
    split; [exact Hroom|]. split; [exact Hlater | exact Hbud].
  + (* g_s[j].pending.n <> 0: the data round *)
    rewrite branch_eq_U, (U_atom E 33 nn E33), (U_lit E 0) in Hc by lia.
    apply Z.eqb_neq in Hc. rename Hc into Hn0.
    destruct Hrecs as [(Hnil & _) | (r0 & rs0 & Erecs & Hoff0 & HoffL)].
    { exfalso. apply Hn0. unfold nn, hl_n. rewrite Hnil. reflexivity. }
    assert (Hs0 : s0 = fst r0) by (unfold s0, tt_hd; rewrite Erecs; reflexivity).
    assert (Hl0 : l0 = Z.of_nat (length (snd r0))) by (unfold l0, tt_hd; rewrite Erecs; reflexivity).
    pose proof Precs as Precs'. rewrite Forall_forall in Precs'.
    destruct (Precs' r0 ltac:(rewrite Erecs; left; reflexivity)) as (Hr0in & Hr0g & _ & Hr0len).
    specialize (Hr0len eq_refl). clear Precs'.
    destruct Pv as [(Hcap0 & _) | (Hcpv & Hvin & Hjv & Hvg)].
    { exfalso. clear - Pn Hcap0 Hn0 Hnn. lia. }
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hr0in) as (_ & Hs4096 & Hsceil & Hsapp & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hvin) as (_ & Hv4096 & Hvceil & Hvapp & _).
    pose proof (tt_req_ge (Z.of_nat (length (snd r0)) + 1)) as Rq0.
    pose proof (tt_req_ge (AREC * hl_cap (hs_pending h1))) as Rqv.
    pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR Hvin) as Hvoff.
    rewrite Erecs in Hvg.
    destruct (tt_vec_rec W1 m1 vv r0 rs0 _ Hvg ltac:(clear - Hs4096 Hsceil Rq0 C1; lia)
      ltac:(clear - Hsceil Rq0 C1 Hs4096; lia)) as (VR0 & VR8).
    pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
      HND1 & HND2 & Hkeys).
    pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
    assert (HUL : ulen sg = re_used e1) by (unfold ulen; rewrite <- Lu, tt_bzs_len; exact HUlen).
    assert (Hcp4 : 4096 + re_used e1 <= re_cap e1) by (clear - Hroom HUL Lcap; rewrite HUL, <- Lcap in Hroom; lia).
    destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [exfalso; clear - Hc0 Hcp4 HUlen; lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
    assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
    assert (Hpend0 : drain_b_c.ds_pend sg = bzs (snd r0) :: map (fun r => bzs (snd r)) rs0)
      by (rewrite <- Lpend, Erecs; reflexivity).
    assert (Hdn : dn = Z.min (l0 - off) (re_cap e1 - re_used e1)).
    { unfold dn, dnum, dhead. rewrite Hpend0, tt_bzs_len, <- Hl0, <- Loff, <- Lcap, HUL. reflexivity. }
    assert (Hcapb : re_cap e1 <= 16384) by (clear - Hcapr; lia).
    assert (Hdnr : 1 <= dn <= 16384) by (clear - Hdn Hoff0 HoffL Hl0 Hcp4 Hcapb HUlen; rewrite Hdn; lia).
    (* ---- 0x8337c .. 0x83388: the shadow address of &g_s[j].pending, re-expressed before its store ---- *)
    paj_run_to_tok RUNTO HS HJ SHOK TTspan A_tt_sh3. { apply awr_ok_x_of0. awr_ok_tac. }
    rename HFr into FR5; rename HG0 into GR5; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msE end.
    assert (KALL5 : forall x, aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
    { intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msD) (ms_mem msE) x)
        by (apply FR5; apply tt_nowr; vm_compute; reflexivity). exact (KALL4 x). }
    assert (PRES5 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msE) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR5 (PRES4 x Hp))).
    tt_reg HS (11%bv : bv 5) X11.
    assert (D11 : getr (ms_regs (restrict (w_H W1) msE)) 11%bv = sv_denot E (tt_shA 23 16)).
    { cbn [ms_regs restrict]. rewrite X11.
      apply (tt_den_resh E GS (Z.of_nat j) 16 E18 E24 E23 E21); clear - GS1 GS2 Hj4'; unfold ASRC in *; lia. }
    pose proof (tt_reseat E _ _ 11%bv _ HS D11 eq_refl) as HS'. clear HS D11 X11. rename HS' into HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
    (* the vector's record, the frame slots the round stores, and the atom facts of the round *)
    assert (E34 : ew E 34 = Z_to_bv 64 vv) by exact (EX 2%nat ltac:(lia)).
    assert (E35 : ew E 35 = Z_to_bv 64 off) by exact (EX 3%nat ltac:(lia)).
    assert (E36 : ew E 36 = Z_to_bv 64 s0) by exact (EX 4%nat ltac:(lia)).
    assert (E37 : ew E 37 = Z_to_bv 64 l0) by exact (EX 5%nat ltac:(lia)).
    assert (E38 : ew E 38 = Z_to_bv 64 dn) by exact (EX 6%nat ltac:(lia)).
    assert (Hvvb : 4096 <= vv /\ vv + 16 <= TT_HI)
      by (clear - Hv4096 Hvceil Rqv C1 Hcpv; unfold TT_HI, AREC in *; lia).
    assert (Hs0b : 4096 <= s0 /\ s0 + l0 < TT_HI)
      by (rewrite Hs0, Hl0; clear - Hs4096 Hsceil Rq0 C1; unfold TT_HI in *; lia).
    assert (Hvva : vv + 16 <= alloc_ceiling) by (clear - Hvceil Rqv Hcpv; unfold AREC in *; lia).
    assert (Hs0a : s0 + l0 + 1 <= alloc_ceiling) by (rewrite Hs0, Hl0; clear - Hsceil Rq0; lia).
    assert (Hl0b : 1 <= l0) by (rewrite Hl0; clear - Hr0len; lia).
    assert (Uvv : bv_unsigned (ew E 34) = vv) by (rewrite E34; apply unsigned_lit_small; clear - Hvvb; unfold TT_HI in *; lia).
    assert (U35 : bv_unsigned (ew E 35) = off) by (rewrite E35; apply unsigned_lit_small; clear - Hoff; lia).
    assert (U36 : bv_unsigned (ew E 36) = s0) by (rewrite E36; apply unsigned_lit_small; clear - Hs0b; unfold TT_HI in *; lia).
    assert (U37 : bv_unsigned (ew E 37) = l0) by (rewrite E37; apply unsigned_lit_small; clear - Hs0b Hl0b; unfold TT_HI in *; lia).
    assert (U38 : bv_unsigned (ew E 38) = dn) by (rewrite E38; apply unsigned_lit_small; clear - Hdnr; lia).
    apply (st_ok_pi_add_fact _ _ _ 34%nat (mkAF 4096 TT_HI 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Uvv, Z.pow_0_r, Z.mod_1_r; clear - Hvvb; lia].
    apply (st_ok_pi_add_fact _ _ _ 36%nat (mkAF 4096 TT_HI 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U36, Z.pow_0_r, Z.mod_1_r; clear - Hs0b Hl0b; lia].
    apply (st_ok_pi_add_fact _ _ _ 37%nat (mkAF 1 TT_HI 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U37, Z.pow_0_r, Z.mod_1_r; clear - Hs0b Hl0b; lia].
    apply (st_ok_pi_add_fact _ _ _ 38%nat (mkAF 1 16384 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U38, Z.pow_0_r, Z.mod_1_r; clear - Hdnr; lia].
    apply (st_ok_pi_add_region _ _ _ tt_vec) in HS;
      [ | vm_compute; reflexivity
        | unfold region_ok, tt_vec;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite Uvv; split; [clear - Hvvb; lia|]; split; [clear - Hvvb; unfold TT_HI in *; lia|];
          split; [intros o Ho; lia|];
          repeat apply Forall_cons; try apply Forall_nil;
          [ apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 36 0) s0);
            [ exact (den_atom0 E 36 s0 E36 ltac:(clear - Hs0b; unfold TT_HI in *; lia)) | zside | zside
            | rewrite Z.add_0_r; apply (tt_vm_kept W1 m1); [intros k Hk; apply KALL5 | rewrite Hs0; exact VR0] ]
          | apply (chunk_ok_val SEGS E _ _ 8 8 (SOff 37 0) l0);
            [ exact (den_atom0 E 37 l0 E37 ltac:(clear - Hs0b Hl0b; unfold TT_HI in *; lia)) | zside | zside
            | apply (tt_vm_kept W1 m1); [intros k Hk; apply KALL5 | rewrite Hl0; exact VR8] ] ]
        | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
          apply all_disjoint_of_extents; unfold extent_of_region, tt_vec;
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uvv, Usp, U23;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
          split; [clear - Hvva HspA; unfold DRAIN_FRAME in *; lia|];
          split; [clear - Hvoff Rqv Hcpv HAr GS1 GS2; unfold off_img, AREC, ASRC in *; lia | exact I] ].
    assert (SWR : forall o, 24 <= o < 208 -> writable_at SEGS (arm W1 (ms_mem msE)) (dsp0 cx - DRAIN_FRAME + o)).
    { pose proof HJ as (_ & _ & (memS & HJi & _) & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. rewrite HDS. unfold DRAIN_FRAME. lia. }
    apply (st_ok_pi_add_region _ _ _ tt_f0) in HS;
      [ | vm_compute; reflexivity
        | unfold region_ok, tt_f0;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite Usp; split; [clear - HspA C1; unfold DRAIN_FRAME in *; lia|];
          split; [clear - HspB; unfold DRAIN_FRAME in *; lia|]; split; [intros o Ho; apply SWR; lia | apply Forall_nil]
        | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
          apply all_disjoint_of_extents; unfold extent_of_region, tt_f0;
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uvv, Usp, U23;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
          split; [clear - Hvva HspA; unfold DRAIN_FRAME in *; lia|];
          split; [lia|];
          split; [clear - HspA HAr GS2 C1; unfold DRAIN_FRAME, ASRC in *; lia | exact I] ].
    apply (st_ok_pi_add_region _ _ _ tt_f2) in HS;
      [ | vm_compute; reflexivity
        | unfold region_ok, tt_f2;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite Usp; split; [clear - HspA C1; unfold DRAIN_FRAME in *; lia|];
          split; [clear - HspB; unfold DRAIN_FRAME in *; lia|]; split; [intros o Ho; apply SWR; lia | apply Forall_nil]
        | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
          apply all_disjoint_of_extents; unfold extent_of_region, tt_f2;
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uvv, Usp, U23;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
          split; [lia|];
          split; [clear - Hvva HspA; unfold DRAIN_FRAME in *; lia|];
          split; [lia|];
          split; [clear - HspA HAr GS2 C1; unfold DRAIN_FRAME, ASRC in *; lia | exact I] ].
    assert (HARE : AR SEGS B ly1 S1 W1 (ms_mem msE) (with_vm_backing (m_vm_lazy _) _ _))
      by (eapply ajournal_gx_AR; exact HJ).
    assert (SHOK2 : sh_ok SEGS (SOff 21 0) TT_SHD E (mrestrict (w_H W1) (ms_mem msE))).
    { unfold sh_ok, TT_SHD. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply (shent_ok_of_range SEGS (w_H W1) (ms_mem msE) E (SOff 21 0) 23 GS (4 * ASRC) HA 0 96).
        + exact (azs_range_addressable B LAWS ly1 S1 W1 (ms_mem msE) _ GS (4 * ASRC) HARE HGSZ).
        + exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
        + apply (U_atom E 23 HA E23). clear - HAr GS1 GS2. unfold ASRC in *. lia.
        + clear - HAr. lia.
        + clear - HAr. lia.
        + intros x Hx. clear - Hx HAr GS1 GS2. unfold SHADOW_OFF, ASRC in *. lia.
      - apply (shent_ok_of_range SEGS (w_H W1) (ms_mem msE) E (SOff 21 0) 34 vv (AREC * hl_cap (hs_pending h1)) vv 0 16).
        + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msE) _ vv (AREC * hl_cap (hs_pending h1))
            vv (AREC * hl_cap (hs_pending h1)) HARE Hvin); [lia | clear - Rqv; lia].
        + exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
        + apply (U_atom E 34 vv E34). clear - Hvvb. unfold TT_HI in *. lia.
        + lia.
        + clear - Hcpv. unfold AREC. lia.
        + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
          clear - Hx Hvapp Hvva Rqv Hcpv C1. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AREC in *. lia. }
    (* ---- 0x83388 .. 0x833b4: shadow(&pending) at 80(sp), v[0].n's shadow check, shadow(&pending_off) ---- *)
    paj_run_to_tok RUNTO HS HJ SHOK2 TTspan A_tt_sh4.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      apply awr_ok_x_cons.
      { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
        left. split; [left; rewrite HDS; unfold DRAIN_FRAME in *; lia | lia]. }
      apply awr_ok_x_cons.
      { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
        left. split; [left; rewrite HDS; unfold DRAIN_FRAME in *; lia | lia]. }
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    rename HFr into FR6; rename HG0 into GR6; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msG end.
    tt_reg HS (14%bv : bv 5) X14b.
    assert (D14b : getr (ms_regs (restrict (w_H W1) msG)) 14%bv = sv_denot E (tt_shA 23 32)).
    { cbn [ms_regs restrict]. rewrite X14b.
      apply (tt_den_resh E GS (Z.of_nat j) 32 E18 E24 E23 E21); clear - GS1 GS2 Hj4'; unfold ASRC in *; lia. }
    pose proof (tt_reseat E _ _ 14%bv _ HS D14b eq_refl) as HS'. clear HS D14b X14b. rename HS' into HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
    (* ---- 0x833b4 .. 0x833cc: n = v[0].n - pending_off, compared with cap - used ---- *)
    paj_run_tok RUN HS HJ SHOK2 TTspan. { tt_awr_regions Usp HDS. }
    rename HFr into FR7; rename HG0 into GR7; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msH end.
    assert (E13 : ew E 13 = Z_to_bv 64 (re_cap e1 - re_used e1))
      by (rewrite (EREG 13%nat 13%bv) by (first [lia | reflexivity]); exact R13).
    assert (U13 : bv_unsigned (ew E 13) = re_cap e1 - re_used e1)
      by (rewrite E13; apply unsigned_lit_small; clear - Hcp4 Hcapb HUlen; lia).
    assert (UC7 : U E (SAlu ALU_ADD (SMd M_MUL (SOff 35 0) (SLit (-1))) (SOff 37 0)) = l0 - off)
      by (apply (tt_U_sub E 35 37 off l0 U35 U37); clear - Hoff0 HoffL Hl0 Hs0b; unfold TT_HI in *; lia).
    assert (Hcu : 0 <= re_cap e1 - re_used e1 < 2 ^ 64) by (clear - Hcp4 Hcapb HUlen; lia).
    (* the views kept so far: the round stored only into the frame slots [24, 88) and [192, 208) *)
    assert (KALLH : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msH) x = aview SEGS (w_H W1) m1 x).
    { intros x Hx N1 N2.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msG) (ms_mem msH) FR7 x Hx)
        by (apply (tt_nowr_fr E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]).
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msE) (ms_mem msG) FR6 x Hx)
        by (apply (tt_nowr_fr E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]).
      exact (KALL5 x). }
    assert (PRESH : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msH) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR7 (apresent_grows _ _ _ _ GR6 (PRES5 x Hp)))).
    clear FR6 FR7 GR6 GR7.
    (* both arms of n = min(...) reach 0x833d4 in the same state (s4 = n, the arm's condition dropped):
       the rest of the round is proved once, as CONT *)
    eassert (CONT : forall (mdx : _) (ms : _), st_ok_pi SEGS VAL E ?[SSN] (restrict (w_H W1) ms) ->
      @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
        (dxmd cx) [] ly1 S1 W1 (ms_mem ms) mdx k1 ->
      sh_ok SEGS (SOff 21 0) TT_SHD E (mrestrict (w_H W1) (ms_mem ms)) ->
      (forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
        ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
        aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x) ->
      (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x) ->
      SRr SEGS W1 (mkCfg ms mdx) (dPOST B MT RG cx)).
    2: {
    psrr_branch_tok RUN BR HS SHOK2 TTspan;
      [ rewrite branch_ltu_U, UC7, (U_atom E 13 (re_cap e1 - re_used e1) E13 Hcu) in Hc;
        apply Z.ltb_lt in Hc;
        assert (Hdn' : dn = l0 - off) by (clear - Hdn Hc; lia);
        paj_run_to_tok RUNTO HS HJ SHOK2 TTspan A_tt_n; [tt_awr_regions Usp HDS|];
        rename HFr into FR8; rename HG0 into GR8; clear HF;
        match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msI end;
        tt_reg HS (20%bv : bv 5) X20;
        assert (D20 : getr (ms_regs (restrict (w_H W1) msI)) 20%bv = sv_denot E (SOff 38 0))
          by (cbn [ms_regs restrict]; rewrite X20, (den_atom0 E 38 dn E38) by (clear - Hdnr; lia);
              rewrite (denot_lit_U E (SAlu ALU_ADD (SMd M_MUL (SOff 35 0) (SLit (-1))) (SOff 37 0))), UC7, Hdn';
              reflexivity)
      | rewrite branch_ltu_U, UC7, (U_atom E 13 (re_cap e1 - re_used e1) E13 Hcu) in Hc;
        apply Z.ltb_ge in Hc;
        assert (Hdn' : dn = re_cap e1 - re_used e1) by (clear - Hdn Hc; lia);
        paj_run_to_tok RUNTO HS HJ SHOK2 TTspan A_tt_n; [tt_awr_regions Usp HDS|];
        rename HFr into FR8; rename HG0 into GR8; clear HF;
        match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msI end;
        tt_reg HS (20%bv : bv 5) X20;
        assert (D20 : getr (ms_regs (restrict (w_H W1) msI)) 20%bv = sv_denot E (SOff 38 0))
          by (cbn [ms_regs restrict]; rewrite X20, (den_atom0 E 38 dn E38) by (clear - Hdnr; lia);
              rewrite (den_atom0 E 13 (re_cap e1 - re_used e1) E13 Hcu), Hdn'; reflexivity) ].
    all: pose proof (tt_reseat E _ _ 20%bv _ HS D20 eq_refl) as HS'; clear HS D20 X20; rename HS' into HS.
    all: pose proof (st_ok_pi_facts_incl E _ _ _ _ HS (fun x Hx => Hx) (fun x Hx => Hx)) as HS'; clear HS;
      rename HS' into HS.
    all: match type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
    all: assert (KALLI : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msI) x = aview SEGS (w_H W1) m1 x)
      by (intros x Hx N1 N2;
          rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msH) (ms_mem msI) FR8 x Hx)
            by (apply (tt_nowr_fr E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]);
          exact (KALLH x Hx N1 N2)).
    all: exact (CONT _ _ HS HJ SHOK2 KALLI (fun x Hp => apresent_grows _ _ _ _ GR8 (PRESH x Hp))). }
    intros mdx msI HSc HJc SHc KALLc PRESc. clear HS HJ SHOK2 KALLH PRESH.
    rename HSc into HS, HJc into HJ, SHc into SHOK2.
    (* ---- 0x833d4 .. 0x833f4: shadow(&pending) at 40(sp), v[0].s's shadow check, the jal to __asan_memcpy ---- *)
    paj_run_tok RUN HS HJ SHOK2 TTspan; [tt_awr_regions Usp HDS|].
    rename HFr into FR9; rename HG0 into GR9; clear HF.
    match type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into msM end.
    assert (KALLM : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msM) x = aview SEGS (w_H W1) m1 x).
    { intros x Hx N1 N2.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msI) (ms_mem msM) FR9 x Hx)
        by (apply (tt_nowr_fr E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]).
      exact (KALLc x Hx N1 N2). }
    assert (PRESM : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msM) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR9 (PRESc x Hp))).
    clear FR9 GR9 KALLc PRESc.
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. tt_reg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    assert (Usp2 : spZ (ms_regs msM) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Usp).
    pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARM.
    (* the relay's buffer is not the vector's block nor the head text's block *)
    pose proof (Permutation_NoDup Hperm (tt_ablocks_nodup _ _ _ _ _ HAR)) as HNDp.
    unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by (clear - Hcpos; lia).
    cbn [app] in HNDp.
    apply List.NoDup_cons_iff in HNDp as [_ HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot _].
    assert (Hvne : (vv, AREC * hl_cap (hs_pending h1)) <> (re_buf e1, re_cap e1)).
    { intros X. apply Hbufnot. rewrite <- X. apply in_or_app. right. apply in_or_app. left.
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks.
      destruct (Z.eqb_spec (hl_cap (hs_pending h1)) 0) as [Hc0|Hc0]; [clear - Hc0 Hcpv; lia|].
      cbn [app]. left. reflexivity. }
    assert (Htne : (fst r0, Z.of_nat (length (snd r0)) + 1) <> (re_buf e1, re_cap e1)).
    { intros X. apply Hbufnot. rewrite <- X. apply in_or_app. right. apply in_or_app. left.
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks.
      destruct (Z.eqb_spec (hl_cap (hs_pending h1)) 0) as [Hc0|Hc0]; [clear - Hc0 Hcpv; lia|].
      cbn [app]. right. rewrite Erecs. cbn [map]. left. reflexivity. }
    pose proof (tt_blk_apart _ _ _ _ _ _ _ _ _ HAR Hr0in Hbin Htne) as Htap. rewrite RQC in Htap.
    pose proof (tt_blk_apart _ _ _ _ _ _ _ _ _ HAR Hvin Hbin Hvne) as Hvap. rewrite RQC in Hvap.
    assert (Hboff : off_img (re_buf e1) (re_cap e1))
      by (pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR Hbin) as X; rewrite RQC in X; exact X).
    assert (Hdnl : off + dn <= l0) by (clear - Hdn Hoff0; rewrite Hdn; lia).
    assert (Hdnc : dn <= re_cap e1 - re_used e1) by (clear - Hdn; rewrite Hdn; lia).
    rewrite RQC in Hbceil.
    destruct HJ as (HSTK2 & HXO2 & (memS2 & HJi2 & HAG2) & HOUT2). rewrite !Z.add_0_r in HJi2.
    (* __asan_memcpy(s->buf + s->used, v[0].s + pending_off, n) *)
    eapply SRr_bind.
    { eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA WS_asan_memcpy) AMEMCPY W1 (ms_regs msM) (ms_mem msM)
        DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS2 (dxmd cx) [] ly1 S1 _ k1
        (re_buf e1 + re_used e1) (s0 + off) dn (- DRAIN_FRAME) _ HJi2).
      - rewrite Q10, (EREG 10%nat 10%bv) by tt_num. exact R10.
      - rewrite Q11, denot_lit_U, U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E 35 off E35), (U_atom E 36 s0 E36) by (clear - Hoff Hs0b; unfold TT_HI in *; lia).
        rewrite zcanon_id by (unfold M64; clear - Hs0b Hoff0 HoffL Hl0; unfold TT_HI in *; lia).
        unfold w64. f_equal. ring.
      - rewrite Q12, E38. reflexivity.
      - clear - Hdnr. lia.
      - clear - Hb4096 HUlen. lia.
      - clear - Hbceil Hdnc C1. lia.
      - rewrite Usp2. ring.
      - unfold DRAIN_FRAME. reflexivity.
      - tt_num.
      - tt_num.
      - rewrite Q3, (EREG 3%nat 3%bv), R3 by tt_num. exact Hgp0.
      - rewrite Q4, (EREG 4%nat 4%bv), R4 by tt_num. exact Htp0.
      - exact Q1.
      - apply ret_ok_codeptr_v; [tt_num | reflexivity].
      - intros a Ha. split; [|clear - Ha Hbceil Hdnc HspA; unfold ESTACK, DRAIN_FRAME; lia].
        assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
        destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
        + right. left. split.
          * apply (Permutation_in _ HPERM0) in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|Hin0];
              [injection X as X1 X2; clear - X2 Hcp4 HUlen; unfold ATABLE, AENT in *; lia|].
            assert (Hin3 : In (re_buf e1, re_cap e1)
              (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
            { apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
              apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
              apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; right; exact X|].
              exfalso. apply Hbufnot. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
              exact Hin0. }
            unfold dFP, dr_fp. apply inFP_cons. right. exists (re_buf e1, re_buf e1 + req_size (re_cap e1)).
            split; [unfold ablocks_fp; exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ Hin3)|].
            cbn [fst snd]. rewrite RQC. clear - Ha Hdnc HUlen. lia.
          * exists (re_buf e1), (re_cap e1). split; [exact Hbin | rewrite RQC; clear - Ha Hdnc HUlen; lia].
        + right. right. left. exists (re_buf e1), (re_cap e1). split; [exact Hbin|].
          split; [exact Hnot0 | rewrite RQC; clear - Ha Hdnc HUlen; lia].
      - apply (tt_amem_range_blk _ _ _ _ _ _ _ _ _ HARM Hbin); [clear - HUlen; lia | clear - Hdnr; lia
        | rewrite RQC; clear - Hdnc; lia].
      - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (re_buf e1) (re_cap e1)
          (re_buf e1 + re_used e1) dn HARM Hbin); [clear - HUlen; lia | rewrite RQC; clear - Hdnc; lia].
      - intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (re_buf e1) (re_cap e1)
          (re_buf e1 + re_used e1) dn HARM Hbin); [clear - HUlen; lia | rewrite RQC; clear - Hdnc; lia | exact Hpos].
      - split; [clear - Hs0b Hoff; lia|]. split; [clear - Hs0b Hdnl Hoff C1; unfold TT_HI in *; lia|].
        split; [|split; [clear - Htap Hs0 Hl0 Hdnl Hdnc Hoff HUlen Rq0; unfold tt_apart in Htap; lia|]].
        + intros a Ha. split; [|rewrite Usp2; clear - Ha Hs0a Hdnl Hoff HspA; unfold ESTACK, DRAIN_FRAME; lia].
          rewrite KALLM by (clear - Ha Hs0a Hs0b Hdnl Hoff HspA C1; unfold TT_HI, DRAIN_FRAME in *; lia).
          replace a with (fst r0 + Z.of_nat (Z.to_nat (a - fst r0))) by (clear - Ha Hs0 Hoff; lia).
          rewrite (tt_garr8_aview W1 m1 _ _ _ Hr0g)
            by (rewrite tt_bzs_len, length_app; cbn [length]; clear - Ha Hs0 Hl0 Hdnl Hoff; lia).
          discriminate.
        + split; [apply (tt_amem_range_blk _ _ _ _ _ _ _ _ _ HARM Hr0in); clear - Hs0 Hl0 Hdnl Hoff Hdnr Rq0; lia|].
          split; [apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (fst r0)
            (Z.of_nat (length (snd r0)) + 1) (s0 + off) dn HARM Hr0in); clear - Hs0 Hl0 Hdnl Hoff Rq0; lia|].
          intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (fst r0)
            (Z.of_nat (length (snd r0)) + 1) (s0 + off) dn HARM Hr0in);
            [clear - Hs0 Hoff; lia | clear - Hs0 Hl0 Hdnl Hoff Rq0; lia | exact Hpos]. }
    cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3i & HP3 & Hd10b & Hcpy & Hfr3 & Hpres3).
    (* ---- after __asan_memcpy ---- *)
    jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
    match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3].
        intros a Ha. apply Hfr3; clear - Ha Hbceil Hdnc HspA HspB C1; unfold ESTACK, DRAIN_FRAME in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3].
        intros a Ha. apply Hfr3; clear - Ha Hbceil Hdnc HspA HspB C1; unfold ESTACK, DRAIN_FRAME in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 34 vv); [exact Uvv | | exact Hpres3].
        intros a Ha. apply Hfr3;
          clear - Ha Hvap Hvvb Hvva Rqv Hcpv Hdnc HUlen HspA C1; unfold tt_apart, AREC, ESTACK, DRAIN_FRAME, TT_HI in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3].
        intros a Ha. apply Hfr3; clear - Ha Hbceil Hdnc HspA HspB C1; unfold ESTACK, DRAIN_FRAME in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 23 HA); [exact U23 | | exact Hpres3].
        intros a Ha. apply Hfr3;
          clear - Ha HAr GS1 GS2 Hboff Hdnc HUlen HspA C1; unfold off_img, ASRC, ESTACK, DRAIN_FRAME in *; lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
    remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
    assert (HEIa : img_env VAL A_LIM Ea)
      by (rewrite HEa; apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
    assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m)
      by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
    clear HEa.
    assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDa by tt_num; exact Usp).
    pose proof (proj1 HJ3i) as HAR3.
    assert (SHOK3 : sh_ok SEGS (SOff 21 0) TT_SHD Ea (mrestrict (w_H W1) mem3)).
    { unfold sh_ok, TT_SHD. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply (shent_ok_of_range SEGS (w_H W1) mem3 Ea (SOff 21 0) 23 GS (4 * ASRC) HA 0 96).
        + exact (azs_range_addressable B LAWS ly1 S1 W1 mem3 _ GS (4 * ASRC) HAR3 HGSZ).
        + apply U_atom; [rewrite OLDa by tt_num; exact E21 | tt_num].
        + apply (U_atom Ea 23 HA); [rewrite OLDa by tt_num; exact E23 | clear - HAr GS1 GS2; unfold ASRC in *; lia].
        + clear - HAr. lia.
        + clear - HAr. lia.
        + intros x Hx. clear - Hx HAr GS1 GS2. unfold SHADOW_OFF, ASRC in *. lia.
      - apply (shent_ok_of_range SEGS (w_H W1) mem3 Ea (SOff 21 0) 34 vv (AREC * hl_cap (hs_pending h1)) vv 0 16).
        + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mem3 _ vv (AREC * hl_cap (hs_pending h1))
            vv (AREC * hl_cap (hs_pending h1)) HAR3 Hvin); [clear - Hvvb; lia | clear - Rqv; lia].
        + apply U_atom; [rewrite OLDa by tt_num; exact E21 | tt_num].
        + apply (U_atom Ea 34 vv); [rewrite OLDa by tt_num; exact E34 | clear - Hvvb; unfold TT_HI in *; lia].
        + clear - Hvvb. lia.
        + clear - Hcpv. unfold AREC. lia.
        + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by (clear - Hcpv Hvvb Rqv; unfold AREC in *; lia).
          clear - Hx Hvapp Hvva Rqv Hcpv C1. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AREC in *. lia. }
    assert (HJ3 : @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
      (dxmem cx) (dxmd cx) [] ly1 S1 W1 mem3 md3 k1).
    { apply (ajournal_gx_pack SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
        (dxmem cx) (dxmd cx) [] ly1 S1 W1 mem3 md3 k1 memS2);
        [exact HSTK2 | tt_num | rewrite !Z.add_0_r; exact HJ3i | exact HAG2 | intros y Hy; clear - Hy; lia]. }
    clear HJ3i HAG2 HOUT2.
    (* ---- 0x833f8 .. 0x8347c: the shadow checks of pending / v / pending_off, the byte loop's registers ---- *)
    paj_run_to_tok RUNTO HS HJ3 SHOK3 TTspan A_dr_feed; [tt_awr_regions UspA HDS|].
    rename HFr into FR10; rename HG0 into GR10; clear HF.
    match type of HS with st_ok_pi _ _ ?EFx _ (restrict _ ?mx) => set (EF := EFx) in HS; rename mx into msF end.
    assert (OLDF : forall m, (m < 48)%nat -> ew EF m = ew E m)
      by (intros m Hm; unfold EF; rewrite ?ew_ewset_other by tt_num; apply OLDa; exact Hm).
    assert (UspF : bv_unsigned (ew EF 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDF by tt_num; exact Usp).
    assert (KALLF : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) mem3 x).
    { intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) mem3 (ms_mem msF) FR10 x Hx).
      apply (tt_nowr_fr Ea _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact UspA | exact N1 | exact N2]. }
    assert (PRESF : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR10 (Hpres3 _ (PRESM x Hp)))).
    clear FR10 GR10.
    (* the n bytes copied: [pending_off, pending_off + n) of the head pending text *)
    set (data := firstn (Z.to_nat dn) (skipn (Z.to_nat off) (snd r0))).
    assert (Hdlen : length data = Z.to_nat dn)
      by (unfold data; rewrite length_firstn, length_skipn; clear - Hdnl Hl0 Hoff Hdnr; lia).
    assert (Hdlj : (length data <= length (re_junk e1))%nat) by (rewrite Hdlen; clear - Hjl Hdnc Hdnr; lia).
    assert (CPY : forall i, (i < length data)%nat ->
      aview SEGS (w_H W1) (ms_mem msF) (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)).
    { intros i Hi. rewrite Hdlen in Hi.
      assert (Hi' : 0 <= Z.of_nat i < dn) by (clear - Hi Hdnr; lia).
      rewrite KALLF by (clear - Hi' Hbceil Hdnc HUlen Hb4096 HspA C1; unfold DRAIN_FRAME in *; lia).
      pose proof (Hcpy (Z.of_nat i) Hi') as Hc. cbv iota in Hc. rewrite Hc.
      rewrite KALLM by (clear - Hi' Hs0a Hs0b Hdnl Hoff HspA C1; unfold TT_HI, DRAIN_FRAME in *; lia).
      replace (s0 + off + Z.of_nat i) with (fst r0 + Z.of_nat (Z.to_nat off + i)) by (clear - Hs0 Hoff; lia).
      rewrite (tt_garr8_aview W1 m1 _ _ _ Hr0g)
        by (rewrite tt_bzs_len, length_app; cbn [length]; clear - Hi Hl0 Hdnl Hoff Hdnr; lia).
      f_equal. unfold data. apply tt_nth_data; [clear - Hl0 Hdnl Hoff Hdnr; lia | exact Hi]. }
    assert (KEEP : forall x, 0 <= x < 2 ^ 64 ->
      ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
      ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
      aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
    { intros x Hx N0 N1 N2 N3. rewrite Hdlen in N0.
      rewrite (KALLF x Hx N1 N2).
      rewrite (Hfr3 x Hx) by (first [clear - N0 Hdnr; lia | clear - N3; lia]).
      exact (KALLM x Hx N1 N2). }
    pose proof (tt_dmem_drb cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 (ms_mem msF) _ data
      HB HMEM HJ3 Hcpos Hdlj KEEP PRESF CPY) as HMEMF.
    (* the frame slots the round stored *)
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF2. cbn [ms_mem restrict] in RF2.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RF0. cbn [ms_mem restrict] in RF0.
    assert (HSAr : 4096 <= SA /\ SA + 56 <= TT_HI)
      by (clear - HGSA HSAG HG4096 HGceil C1; unfold TT_HI, AENT, ATABLE in *; lia).
    assert (R64 : forall v, 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N 8)) by (intros v Hv; exact Hv).
    assert (F18 : ew EF 18 = Z_to_bv 64 GS) by (rewrite OLDF by tt_num; exact E18).
    assert (F21 : ew EF 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDF by tt_num; exact E21).
    assert (F22 : ew EF 22 = Z_to_bv 64 SA) by (rewrite OLDF by tt_num; exact E22).
    assert (F23 : ew EF 23 = Z_to_bv 64 HA) by (rewrite OLDF by tt_num; exact E23).
    assert (F24 : ew EF 24 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat j)) by (rewrite OLDF by tt_num; exact E24).
    assert (F25 : ew EF 25 = Z_to_bv 64 (SA + 32))
      by (rewrite OLDF, (EREG 25%nat 25%bv) by tt_num; exact R25).
    assert (F26 : ew EF 26 = Z_to_bv 64 (SA + 16))
      by (rewrite OLDF, (EREG 26%nat 26%bv) by tt_num; exact R26).
    assert (F27 : ew EF 27 = Z_to_bv 64 (SA + 24))
      by (rewrite OLDF, (EREG 27%nat 27%bv) by tt_num; exact R27).
    assert (F35 : ew EF 35 = Z_to_bv 64 off) by (rewrite OLDF by tt_num; exact E35).
    assert (F36 : ew EF 36 = Z_to_bv 64 s0) by (rewrite OLDF by tt_num; exact E36).
    assert (F38 : ew EF 38 = Z_to_bv 64 dn) by (rewrite OLDF by tt_num; exact E38).
    assert (HAb : 0 <= HA /\ HA + 96 < 2 ^ 47) by (clear - HAr GS1 GS2; unfold ASRC in *; lia).
    assert (Heif : drain_b_c.ds_eintr sg = false)
      by (unfold ei in Hei0; rewrite Hei0 in Lei; destruct (drain_b_c.ds_eintr sg); [discriminate | reflexivity]).
    assert (Hpne : drain_b_c.ds_pend sg <> []) by (rewrite Hpend0; discriminate).
    assert (Hstr : dstrict sg).
    { intros r rs Hrs. rewrite Hpend0 in Hrs. injection Hrs as <- _. rewrite tt_bzs_len, <- Loff.
      clear - HoffL. lia. }
    pmkst HS.
    prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3. prreg HS (4%bv : bv 5) Y4.
    prreg HS (8%bv : bv 5) Y8. prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18.
    prreg HS (19%bv : bv 5) Y19. prreg HS (21%bv : bv 5) Y21. prreg HS (23%bv : bv 5) Y23.
    prreg HS (25%bv : bv 5) Y25.
    tt_reg HS (20%bv : bv 5) Y20. tt_reg HS (22%bv : bv 5) Y22. tt_reg HS (24%bv : bv 5) Y24.
    tt_reg HS (26%bv : bv 5) Y26. tt_reg HS (27%bv : bv 5) Y27.
    rewrite ?OLDF in Y2, Y3, Y4, Y8, Y9, Y18, Y19, Y21, Y23, Y25 by tt_num.
    match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
    apply (Krb W1). unfold DRB.
    exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, (tt_junk e1 (data ++ skipn (length data) (re_junk e1))),
      h1, out1, ev1, LB1, spent, jb, aa, (drain_b_c.da_ev aa), (drain_b_c.da_erecs aa), tl, (s0 + off), r0, rs0.
    split; [unfold cfg_at; reflexivity|].
    split; [unfold spZ; rewrite Y2, (EREG 2%nat 2%bv) by tt_num; exact Hsp|].
    split; [rewrite Y3, (EREG 3%nat 3%bv) by tt_num; exact R3|].
    split; [rewrite Y4, (EREG 4%nat 4%bv) by tt_num; exact R4|].
    split; [rewrite Y18, E18; reflexivity|].
    split; [rewrite Y9, (EREG 9%nat 9%bv) by tt_num; exact R9|].
    split; [rewrite Y8, (EREG 8%nat 8%bv) by tt_num; exact R8|].
    split; [rewrite Y21, E21; reflexivity|].
    split; [rewrite Y23, E23; reflexivity|].
    split; [rewrite Y19, E38; reflexivity|].
    split; [rewrite Y25, E38; change (Z.of_nat 0) with 0; rewrite Z.sub_0_r; reflexivity|].
    split; [rewrite Y26, denot_lit_U, U_SAlu; cbn [zalu_raw];
      rewrite (U_atom EF 35 off F35), (U_atom EF 36 s0 F36) by (clear - Hoff Hs0b; unfold TT_HI in *; lia);
      rewrite zcanon_id by (unfold M64; clear - Hs0b Hdnl Hdnr Hoff; unfold TT_HI in *; lia);
      unfold w64; f_equal; change (Z.of_nat 0) with 0; ring|].
    split; [rewrite Y24, denot_lit_U, U_SAlu; cbn [zalu_raw];
      rewrite (U_atom EF 35 off F35), (U_atom EF 36 s0 F36) by (clear - Hoff Hs0b; unfold TT_HI in *; lia);
      rewrite zcanon_id by (unfold M64; clear - Hs0b Hdnl Hdnr Hoff; unfold TT_HI in *; lia);
      unfold w64; f_equal; change (Z.of_nat 0) with 0; ring|].
    split; [rewrite Y20, (tt_den_resh EF GS (Z.of_nat j) 40 F18 F24 F23 F21), (tt_den_shA EF 23 HA 40 F23 F21)
      by (clear - HAb HAr GS1 GS2 Hj4'; unfold ASRC in *; lia); reflexivity|].
    split; [rewrite Y27, (tt_den_resh EF GS (Z.of_nat j) 48 F18 F24 F23 F21), (tt_den_shA EF 23 HA 48 F23 F21)
      by (clear - HAb HAr GS1 GS2 Hj4'; unfold ASRC in *; lia); reflexivity|].
    split; [rewrite Y22, (tt_den_resh EF GS (Z.of_nat j) 56 F18 F24 F23 F21), (tt_den_shA EF 23 HA 56 F23 F21)
      by (clear - HAb HAr GS1 GS2 Hj4'; unfold ASRC in *; lia); reflexivity|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 HMEMF)))))|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 56 8%N (SOff 22 0) SA RF0 UspF);
      [repeat (first [left; reflexivity | right]) | exact (den_atom0 EF 22 SA F22 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 64 8%N (SOff 25 0) (SA + 32) RF0 UspF);
      [repeat (first [left; reflexivity | right])
      | exact (den_atom0 EF 25 (SA + 32) F25 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 48 8%N (SOff 27 0) (SA + 24) RF0 UspF);
      [repeat (first [left; reflexivity | right])
      | exact (den_atom0 EF 27 (SA + 24) F27 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 192 208 192 208 200 8%N (SOff 26 0) (SA + 16)
        RF2 UspF);
      [repeat (first [left; reflexivity | right])
      | exact (den_atom0 EF 26 (SA + 16) F26 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 32 8%N (SOff 23 24) (HA + 24) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_off; [exact F23 | clear - HAb; lia | clear - HAb; lia]
      | apply R64; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 24 8%N (SOff 23 56) (HA + 56) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_off; [exact F23 | clear - HAb; lia | clear - HAb; lia]
      | apply R64; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 72 8%N (SOff 23 64) (HA + 64) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_off; [exact F23 | clear - HAb; lia | clear - HAb; lia]
      | apply R64; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 80 8%N (tt_shA 23 16)
        (shadow_addr (HA + 16)) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_shA; [exact F23 | exact F21 | clear - HAb; lia | clear - HAb; lia]
      | apply R64, tt_sh_range; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 40 8%N (tt_shA 23 24)
        (shadow_addr (HA + 24)) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_shA; [exact F23 | exact F21 | clear - HAb; lia | clear - HAb; lia]
      | apply R64, tt_sh_range; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 192 208 192 208 192 8%N (tt_shA 23 32)
        (shadow_addr (HA + 32)) RF2 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_shA; [exact F23 | exact F21 | clear - HAb; lia | clear - HAb; lia]
      | apply R64, tt_sh_range; clear - HAb; lia | tt_num]|].
    split; [exact Erecs|].
    split; [clear - Hs0 Loff; lia|].
    split; [change (dnum sg) with dn; clear - Hdnr; lia|].
    split; [change (dnum sg) with dn; clear - Hdnr; lia|].
    split.
    { cbn [tt_junk re_junk]. change (dnum sg) with dn.
      rewrite firstn_app, Hdlen, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite Hdlen; apply le_n).
      unfold data, ddata, dhead. rewrite Hpend0, <- Loff. cbv iota.
      rewrite tt_skipn_bzs, tt_firstn_bzs. reflexivity. }
    split; [exact HMEMF|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HSAME|].
    split; [exact Lcap|]. split; [exact Lu|]. split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|].
    split; [exact Hei0|]. split; [exact Lpend|]. split; [exact Loff|]. split; [exact Lst|].
    split; [change (Z.of_nat (length (lines (drain_b_c.ds_ref sg) (firstn 0 (ddata sg))))) with 0;
      rewrite Z.add_0_r; exact Len|].
    split; [exact Lecap|].
    split; [change (firstn 0 (ddata sg)) with (@nil Z); rewrite app_nil_r; exact HHIST|].
    split.
    { unfold RSTART. split; [exact (proj1 (proj2 HHIST))|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Lwf|]. split; [exact Hstr|]. split; [exact Heif | exact Hpne]. }
    split; [exact (tt_dpfut0 cx sg jb aa tl Hlater Heif Hpne Hstr Hroom) | exact Hbud].
- (* g_s[j].eintr == 1: the EINTR round *)
  rewrite branch_eq_U, (U_atom E 32 ei E32), (U_lit E 0) in Hc by (unfold ei in *; lia).
  apply Z.eqb_neq in Hc. assert (Hei1 : ei = 1) by (clear - Hc Hei01; unfold ei in *; lia).
  (* the slot's region gets its write window over g_s[j].eintr *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG0.
  assert (RG1 : region_ok SEGS E (ms_mem (restrict (w_H W1) msB)) (set_window tt_g0 12 16)).
  { apply region_ok_rewindow; [exact RG0|]. cbn [YP09.r_base tt_g0 base_val ms_mem restrict]. rewrite U23.
    intros o Ho. apply (writable_kept (w_H W1) m1 (ms_mem msB)).
    - exact (PRES2 _).
    - exact (HAWS o ltac:(unfold ASRC; lia)). }
  pose proof (ast_ok_pi_set_region E _ _ 1 tt_g0 (set_window tt_g0 12 16) HS eq_refl eq_refl eq_refl RG1) as HS'.
  clear HS RG0 RG1. rename HS' into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond list_upd] in HS.
  (* ---- 0x83330 .. 0x8333c: the store eintr = 0, the jal to __errno_location ---- *)
  paj_run_tok RUN HS HJ SHOK TTspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
    unfold G_DR, G_SL, inG; cbn [In]. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha HAr. unfold ASRC in *. lia. }
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  match type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into msC end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  (* __errno_location: writes nothing, returns tp - 164 *)
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs msC) (ms_mem msC) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ).
    - unfold spZ at 1. rewrite Q2, Usp. lia.
    - unfold DRAIN_FRAME. reflexivity.
    - unfold DRAIN_FRAME. lia.
    - lia.
    - rewrite HDS. unfold ESTACK, DRAIN_FRAME. lia.
    - rewrite Q3, (EREG 3%nat 3%bv), R3 by (first [lia | reflexivity]). exact Hgp0.
    - rewrite Q4, (EREG 4%nat 4%bv), R4 by (first [lia | reflexivity]). exact Htp0.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros _. right. intros [].
    - intros a [].
    - intros a [].
    - intros HPRE _. exact (AERRNO ly1 S1 W1 (ms_regs msC) (ms_mem msC) _ HPRE). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat; 1%nat] HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres2].
      intros a Ha. apply Hfr2; [lia | intros [] | unfold ESTACK, DRAIN_FRAME in *; lia].
    - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 23 HA); [exact U23 | | exact Hpres2].
      intros a Ha. apply Hfr2; [unfold ASRC in *; lia | intros [] | unfold ESTACK, DRAIN_FRAME, ASRC in *; lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  clear HEa.
  prreg HS (10%bv : bv 5) R10a.
  assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
  { assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
    { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
        repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
    pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as PI0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as PI3.
    lia. }
  assert (F52 : ew Ea 52 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10a, Herr, HERRNO; reflexivity).
  assert (B52 : bv_unsigned (ew Ea 52) = as_errno B) by (rewrite F52; apply unsigned_lit_small; lia).
  apply (st_ok_pi_add_fact _ _ _ 52%nat (mkAF 0x10000 0x5fb000 0)) in HS;
    [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B52, Z.pow_0_r, Z.mod_1_r; lia ].
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VERR & AWERR & _).
  apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 52%nat) 0 4 0 4 [])) in HS;
    [ | vm_compute; reflexivity
      | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite B52; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
        [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR3); apply (apresent_grows _ _ _ _ GR2);
          apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (AWERR o Ho) ]
      | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
        apply all_disjoint_of_extents; unfold extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B52, (OLDa 2%nat), (OLDa 23%nat), Usp, U23 by lia;
        cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
        split; [clear - HERRI HspA C1; unfold DRAIN_FRAME in *; lia|];
        split; [pose proof tt_errno_gs as TEG; clear - TEG HAr; unfold ASRC in *; lia | exact I] ].
  assert (UBa : U Ea (SOff 21 0) = SHADOW_OFF)
    by (apply U_atom; [rewrite (OLDa 21%nat) by lia; exact E21 | unfold SHADOW_OFF; lia]).
  assert (SHOK3 : sh_ok SEGS (SOff 21 0) [mkSHE 52 0 4] Ea (mrestrict (w_H W1) mem2)).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea (SOff 21 0) 52%nat (as_errno B) 4 (as_errno B) 0 4).
    - apply (azs_range_addressable B LAWS ly1 S1 W1 mem2 md2 (as_errno B) 4);
        [exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) | exact HERRZ].
    - exact UBa.
    - apply U_atom; [exact F52 | lia].
    - lia.
    - lia.
    - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF. lia. }
  (* ---- 0x83340 .. 0x83360: the shadow check of errno folds, errno = EINTR, s7 / s8 reloaded, back to the head ---- *)
  paj_run_to_tok RUNTO HS HJ2 SHOK3 TTspan A_dr_top.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B52 in Ha.
      unfold G_DR, G_SL, inG; cbn [In].
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]. }
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite (OLDa 23%nat), U23 in Ha by lia.
    unfold G_DR, G_SL, inG; cbn [In]. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha HAr. unfold ASRC in *. lia. }
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  (* what the round kept: every view but g_s[j].eintr, errno and the callee's scratch *)
  assert (KEEPE : forall x, 0 <= x < 2 ^ 64 -> ~ (HA + 12 <= x < HA + 16) -> ~ (as_errno B <= x < as_errno B + 4) ->
    ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
  { intros x Hx N1 N2 N3.
    rewrite (aview_kept_out _ _ (w_H W1) mem2 (ms_mem msF) FR4 x Hx).
    2:{ intros (r & Hin & Hr). vm_compute in Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite ?(OLDa 23%nat), ?U23, ?B52 in Hr by lia; lia. }
    rewrite (Hfr2 x Hx (fun f => f) ltac:(clear - N3; lia)).
    rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msB) (ms_mem msC) FR3 x Hx).
    2:{ intros (r & Hin & Hr). vm_compute in Hin.
        destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?U23 in Hr; lia. }
    exact (KALL2 x). }
  assert (PRESE : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
    by (intros x Hp; exact (apresent_grows _ _ _ _ GR4 (Hpres2 _ (apresent_grows _ _ _ _ GR3 (PRES2 x Hp))))).
  match type of HS with st_ok_pi _ _ ?EFx _ _ => set (EF := EFx) in HS end.
  assert (OLDF : forall m, (m < 48)%nat -> ew EF m = ew E m)
    by (intros m Hm; unfold EF; rewrite ?ew_ewset_other by lia; apply OLDa; exact Hm).
  assert (U23F : bv_unsigned (ew EF 23) = HA) by (rewrite OLDF by lia; exact U23).
  assert (B52F : bv_unsigned (ew EF 52) = as_errno B) by (unfold EF; rewrite ?ew_ewset_other by lia; exact B52).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RGE. cbn [ms_mem restrict] in RGE.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RGG. cbn [ms_mem restrict] in RGG.
  assert (VERRF : val_mem SEGS (arm W1 (ms_mem msF)) (as_errno B) 4 4).
  { pose proof (field_of_region EF _ 52%nat (as_errno B) _ 0 4 0 4 0 4%N (SLit 4) 4 RGE B52F) as VF.
    rewrite Z.add_0_r in VF. apply VF; [left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
  assert (V12F : val_mem SEGS (arm W1 (ms_mem msF)) (HA + 12) 4 0).
  { apply (field_of_region EF _ 23%nat HA _ 12 40 12 16 12 4%N (SLit 0) 0 RGG U23F);
      [left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3. prreg HS (4%bv : bv 5) Y4.
  prreg HS (8%bv : bv 5) Y8. prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18.
  prreg HS (21%bv : bv 5) Y21. prreg HS (22%bv : bv 5) Y22. prreg HS (25%bv : bv 5) Y25.
  prreg HS (26%bv : bv 5) Y26. prreg HS (27%bv : bv 5) Y27.
  tt_reg HS (23%bv : bv 5) Y23. tt_reg HS (24%bv : bv 5) Y24.
  rewrite ?OLDF, ?OLDa in Y2, Y3, Y4, Y8, Y9, Y18, Y21, Y22, Y25, Y26, Y27 by lia.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr. apply EREG; assumption. }
  pose proof (tt_dmem_eintr cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 (ms_mem msF) _ HB HMEM HJ2
    KEEPE PRESE V12F VERRF) as HMEMF.
  pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
  assert (HEIT : drain_b_c.ds_eintr sg = true)
    by (unfold ei in Hei1; rewrite Hei1 in Lei; destruct (drain_b_c.ds_eintr sg); [reflexivity | discriminate]).
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  apply (Kdi HEIT W1). unfold DI.
  exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, e1, (tt_clr_ei h1), out1, 4, LB1, spent, jb, aa, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite (RK _ 2%nat Y2) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite (RK _ 3%nat Y3) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite (RK _ 4%nat Y4) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite (RK _ 22%nat Y22) by (first [lia | reflexivity]); exact R22|].
    split; [rewrite (RK _ 25%nat Y25) by (first [lia | reflexivity]); exact R25|].
    split; [rewrite (RK _ 27%nat Y27) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite (RK _ 26%nat Y26) by (first [lia | reflexivity]); exact R26|].
    split; [rewrite (RK _ 18%nat Y18) by (first [lia | reflexivity]); exact R18|].
    split; [rewrite (RK _ 9%nat Y9) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite (RK _ 8%nat Y8) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite (RK _ 21%nat Y21) by (first [lia | reflexivity]); exact R21|].
    split.
    - rewrite Y23. apply (tt_den_shA EF 22 SA 32); [rewrite OLDF by lia; exact E22 | rewrite OLDF by lia; exact E21
      | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia
      | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia].
    - rewrite Y24. rewrite (tt_den_shA EF 22 SA 0); [rewrite Z.add_0_r; reflexivity | rewrite OLDF by lia; exact E22
      | rewrite OLDF by lia; exact E21 | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia
      | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia]. }
  split; [exact HMEMF|].
  split; [exact HnoNUL|]. split; [exact Hused|].
  split.
  { unfold DLINK. cbn [tt_clr_ei hs_eintr]. unfold dclr. cbn [drain_b_c.ds_eintr].
    split; [exact Lcap|]. split; [exact Lu|]. split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|].
    split; [reflexivity|]. split; [exact Lpend|]. split; [exact Loff|]. split; [exact Lst|].
    split; [exact Len|]. split; [exact Lecap | exact Lwf]. }
  split; [exact HSAME|]. split; [exact HHIST|]. split; [exact HJ1|].
  split; [exact (tt_dlater_eintr cx sg jb aa tl Hlater HEIT Hroom) | exact Hbud].
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice A, 2026-10-30): dr_toptail_x proves W_drain_topb_cx.v's
   dr_toptail_stmt_x over W_drain_cx_x.v's Section variables (the allocator rules in their caller-context forms; the
   tail calls no allocator).  HP0 serves the block shadow facts of the __asan_memcpy call and of the vector's shadow
   check (W_journal_x's *_of_block_hp0_x), BLKN the size bound tt_blk_apart_x / tt_ablocks_nodup_x read (cgif's
   al_blocks carried it, alx_blocks does not).  A live block's bytes are off the image by YCbqG.blk_img_x and the
   walk's g_s / errno cells are image bytes by HG, so no image-cover hypothesis is taken (tt_blk_gs_x,
   tt_aout_fp_img).  The two callees, __errno_location and __asan_memcpy, keep the caller's allocator state and
   ghost list, so the cut's ghost list Hp1 and its dbud_x (room and counts at ly1 / S1 / tl) carry unchanged from
   DT2_x to DI_x / DEND_x / DRB_x.
   Everything above is unchanged.  The AR-free names of Section c above are CITED with the Section variables they
   abstracted; the lemmas whose statements or proofs name AR, the journal, DMEM, the cuts or the run chain have
   their _x twin here (same name with _x when the AR name exists). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_laws_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again; and the scopes
   this file opens, again on top of the ones the imports above open *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

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
(* the instance's laws *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
(* the walk's globals, the allocator's statics, errno and the sink's overflow head are never read-only image
   bytes: what a callee's journal may change is disjoint from ROM, so rom_view survives it (W_journal.v
   rom_out / ajournal_gx_rom_view).  The pinned placement decides it by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites_x.v / W_drain_cx_x.v Section r) *)
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
(* memchr: the shared general text (dis-7's amemchr_realizesM, lib/Rt/MemchrDef.v; proved on our image by R3 as
   memchr_icpt_realizesM), over ARx (W_drain_cx_x.v amemchr_realizesM_x).  Its constant window is the musl memchr's
   masks at 0x10350 .. 0x10370 (HCROM). *)
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
(* The allocator's site rules in their caller-context forms over the generic journal (W_journal_x.v Section hc), at
   RP, ONE context table per allocator entry (the instance proves each rule at its own table: top_x's CTX_AREALLOC,
   CTX_AFREE and strndup's).  Every drain site hands the rule a cut chain (ch = []), so each trace is the return
   address alone; the walk that calls takes that site's closed In fact (the HCTX facts).  This segment makes no
   allocator call. *)
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
(* the allocator instance's granule-tail fact is no hypothesis: W_drain_cx_x.v alloc_tail_x, a theorem of LAWS *)
(* the callees drain calls as a program (W_contract_x.v), at RP *)
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
(* the room round's budget law (W_drain_cx_x.v RMM) *)
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
(* instance facts *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
(* placement of the three output cells aout_at reads that are not in G_DR's g_s range (W_drain_cx.v HV9 / HV12 / HSM) *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* a register read off a symbolic state, with its value left as the state's own expression *)
Ltac tt_reg HS r Hr :=
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
Ltac tt_len := rewrite ?length_app, ?tt_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes;
  cbn [length].

Lemma tt_blk_apart_x : forall ly S hp (W : world SEGS) mem md p n q m,
ARx ly S hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
tt_apart p (req_size n) q (req_size m).
Proof.
intros ly S hp W mem md p n q m HAR Hp Hq Hne.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hk) as Hk0.
  exact (proj1 (req_size_pos k ltac:(lia))). }
pose proof ((tt_pw_nodup RG) _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (tt_nodup_map_inj f _ _ _ Hnd Hp Hq E))).
destruct (tt_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hp) (in_map f _ _ Hq) Hf) as [X|X];
  unfold tt_apart, zdisjoint, f in *; cbn [fst snd] in X; lia.
Qed.
Lemma tt_ablocks_nodup_x : forall ly S hp (W : world SEGS) mem md, ARx ly S hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S hp W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hp : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hk) as Hk0.
  exact (proj1 (req_size_pos k ltac:(lia))). }
rewrite <- Eb. exact (NoDup_map_inv f _ ((tt_pw_nodup RG) _ Hpos Hpw)).
Qed.
Lemma tt_blk_noimg_x : forall ly S hp (W : world SEGS) mem md q m a,
ARx ly S hp W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S hp W mem md q m a HAR Hin Ha.
exact (blk_img_x SEGS B ARx LAWS ly S hp W mem md q m a HAR Hin Ha).
Qed.
(* a live block is apart from every range of g_s: its bytes are off the image (blk_img_x), g_s's are image bytes (HG);
   this replaces cgif's image-band reading of a block (blk_off_imgP), whose cover fact a generic ARx does not give *)
Lemma tt_blk_gs_x : forall ly S hp (W : world SEGS) mem md q m a n,
ARx ly S hp W mem md -> In (q, m) (ablocks B ly S) -> rg_s RG <= a -> a + n <= rg_s RG + 4 * ASRC -> 0 < n ->
tt_apart q (req_size m) a n.
Proof.
intros ly S hp W mem md q m a n HAR Hin Ha1 Ha2 Hn.
pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hin) as Hm0. pose proof (req_size_pos m Hm0) as [Hr1 _].
unfold tt_apart.
destruct (Z_le_gt_dec (q + req_size m) a) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (a + n) q) as [H2|H2]; [right; exact H2|].
exfalso. apply (tt_blk_noimg_x ly S hp W mem md q m (Z.max q a) HAR Hin ltac:(lia)).
apply (proj1 (HG (Z.max q a) ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))).
Qed.
Lemma tt_amem_range_blk_x : forall ly S hp (W : world SEGS) mem md q m a n,
ARx ly S hp W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> 0 <= n -> a + n <= q + req_size m ->
amem_range a n.
Proof.
intros ly S hp W mem md q m a n HAR Hin H1 H2 H3.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q m HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Local Ltac tt_infp := repeat (first [left; reflexivity | right]).
(* the same footprint read against the image: each cell of the controller is an image byte (HG / HGO), the rest is the
   output block *)
Lemma tt_aout_fp_img : forall cap out r, In r (aout_fp B RG cap out) -> forall x, fst r <= x < snd r ->
in_img SEGS x \/ exists q m, In (q, m) (aout_blks cap out) /\ q <= x < q + m.
Proof.
intros cap out r Hr x Hx.
assert (GD : forall b l, In (b, l) (G_DR B RG) -> b <= x < b + l -> in_img SEGS x).
{ intros b l Hb Hbx. apply (proj1 (HG x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
assert (GO : forall b l, In (b, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] ->
  b <= x < b + l -> in_img SEGS x).
{ intros b l Hb Hbx. apply (proj1 (HGO x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Hx.
- left. apply (GO (rg_send_max RG) 8); [tt_infp | lia].
- left. apply (GD (rg_nout RG) 8); [unfold G_DR, G_SL; tt_infp | lia].
- left. apply (GD (rg_capout RG) 8); [unfold G_DR, G_SL; tt_infp | lia].
- left. apply (GD (rg_out RG) 8); [unfold G_DR, G_SL; tt_infp | lia].
- left. apply (GO (rg_client RG) 4); [tt_infp | lia].
- left. apply (GD (rg_client_broken RG) 1); [unfold G_DR, G_SL; tt_infp | lia].
- left. apply (GO (rg_send_dead RG) 1); [tt_infp | lia].
- left. apply (GD (rg_send_eintr RG) 1); [unfold G_DR, G_SL; tt_infp | lia].
- left. apply (GD (as_errno B) 4); [unfold G_DR, G_SL; tt_infp | lia].
- destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  right. exists out, cap. split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity | lia].
Qed.



(* a side goal between numerals, decided by computation: lia would scan (and case-split) the whole context *)
Ltac tt_num := repeat match goal with |- _ /\ _ => split end;
  first [ reflexivity | apply Nat.ltb_lt; vm_compute; reflexivity | apply Nat.leb_le; vm_compute; reflexivity
        | apply Z.ltb_lt; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity ].

(* the write obligation of a run whose windows are read-only or drain's own frame slots *)
Ltac tt_awr_regions Usp HDS :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_x_nil
  | apply awr_ok_x_cons; [intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia|]
  | apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
      left; split; [left; rewrite HDS; unfold DRAIN_FRAME in *; clear - Ha; lia | clear - Ha; lia] |] ].



(* ---- route R: the R twin of each piece of Section cx whose statement names the journal, SRr, a carrier or
   a statement: the strict text with the journal and SRr at R and each carrier / statement / engine lemma at its R
   twin (W_drain_cx_x.v Section wR). The strict lemmas above are unchanged. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Lemma tt_DMEM_kept_xR : forall cx hp ly1 S1 hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx hp ly1 S1 hp1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 HMEM HJ2 KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (Hkept : forall a, abyte_kept W1 m1 W1 m2 a).
{ intros a. split; [exact (KL a)|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKA : forall fp, akept W1 m1 W1 m2 fp) by (intros fp r Hr a Ha; exact (Hkept a)).
assert (HVM : forall a n v, val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v H. apply (akept_vm W1 m1); [intros x Hx; exact (Hkept x) | exact H]. }
split; [exact HJ2|].
split; [intros a Ha; rewrite (KL a); exact (Hrom a Ha)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & ASV).
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVM; assumption | intros i Hi; apply HVM; exact (ASV i Hi) ]. }
split; [exact (tt_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => KL x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact ((tt_aentry_okx_kept B RG) ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  ((tt_aentry_blks_in B RG HGSB) ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  ((tt_asrc_blks_in B RG HGSB) ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact ((tt_aout_blks_in B RG HGSB) ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.

Lemma tt_dmem_eintr_xR : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF,
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) -> ~ (as_errno B <= x < as_errno B + 4) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
val_mem SEGS (arm W1 mF) (dHA RG cx + 12) 4 0 ->
val_mem SEGS (arm W1 mF) (as_errno B) 4 4 ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 mF mdF k1 e1 (tt_clr_ei h1) (dclr sg) out1 4 sent LB1.
Proof.
intros cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF HB HMEM HJF KEEP PRES V12 VERR.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : ARx ly1 S1 hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx)
  by (unfold dsp0; clear - Hslo Hceil; change DRAIN_STK_x with 16976 in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
pose proof HGSB as (GS1 & GS2 & GS3).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; clear - Hj4; lia).
assert (GIMG : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GSG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (ERG : forall x, as_errno B <= x < as_errno B + 4 -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]).
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
{ pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B) ltac:(lia)))) as P0.
  pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B + 3) ltac:(lia)))) as P3. lia. }
pose proof (tt_errno_gs B RG HRGD) as TEG.
assert (KB : forall x, 0 <= x < alloc_ceiling -> ~ in_img SEGS x -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx Hni. split.
  - apply KEEP; [clear - Hx C1; lia | intros Hy; apply Hni, GIMG, GSG; clear - Hy HAr; lia
    | intros Hy; apply Hni, GIMG, ERG; exact Hy | clear - Hx HspA; unfold ESTACK, DRAIN_FRAME; lia].
  - unfold arm. apply writable_kept. apply PRES. }
assert (KI : forall x, 0x10000 <= x < 0x5fb000 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx N1 N2. split.
  - apply KEEP; [lia | exact N1 | exact N2 | clear - Hx HspA C1; unfold ESTACK, DRAIN_FRAME; lia].
  - unfold arm. apply writable_kept. apply PRES. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. split.
  - apply KEEP; [clear - Hx HspA HspB C1; unfold DRAIN_FRAME in *; lia
    | clear - Hx HspA HAr GS2 C1; unfold DRAIN_FRAME, ASRC in *; lia
    | clear - Hx HspA HERRI C1; unfold DRAIN_FRAME in *; lia | lia].
  - unfold arm. apply writable_kept. apply PRES. }
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> q <= x < q + n -> abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hx. destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof ((tt_req_ge RG) n) as Rq. apply KB; [clear - Hx H4 Hc Rq; lia|].
  apply (tt_blk_noimg_x _ _ _ _ _ _ q n x HAR Hin). clear - Hx Rq. lia. }
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept _ m1 mF x (PRES x) Hw)).
pose proof HEOK as (_ & _ & Hpad1 & Hpad2 & _).
split; [exact HJF|].
split.
{ intros x Hx. pose proof (pa_img_range _ (tt_rom_img x Hx)) as Hxr. rewrite KEEP; [exact (Hrom x Hx) | lia
  | intros Hy; apply (HGR x); [apply GSG; clear - Hy HAr; lia | exact Hx]
  | intros Hy; apply (HGR x); [apply ERG; exact Hy | exact Hx]
  | clear - Hxr HspA C1; unfold ESTACK, DRAIN_FRAME; lia]. }
split; [intros a Ha1 Ha2 Ha3 Ha4; apply PRES; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & ASV).
  assert (HVM : forall o n v, 0 <= o -> o + Z.of_nat n <= DRAIN_FRAME ->
    val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o) n v -> val_mem SEGS (arm W1 mF) (dsp0 cx - DRAIN_FRAME + o) n v)
    by (intros o n v Ho Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply KFR; lia | exact Hv]).
  repeat match goal with |- _ /\ _ => split end;
    try (apply HVM; [lia | cbn; unfold DRAIN_FRAME; lia | assumption]).
  intros i Hi. specialize (ASV i Hi).
  replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i))
    in ASV |- * by lia.
  apply HVM; [lia | cbn; unfold DRAIN_FRAME; lia | exact ASV]. }
split.
{ apply (tt_garr8_kept W1 m1 W1 mF _ _ Hgarr). intros x Hx. rewrite (tt_entry_len e1 Hpad1 Hpad2) in Hx.
  apply (proj1 (KBL (dxG cx) ATABLE x HGin1 ltac:(clear - Hx HGSA HSAG; unfold AENT, ATABLE in *; lia))). }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ apply ((tt_aentry_okx_kept B RG) ly1 S1 W1 m1 ly1 S1 W1 mF e1 HEOK); [|exact ((tt_aentry_blks_in B RG HGSB) ly1 S1 W1 m1 e1 HEOK)].
  intros r Hr x Hx. destruct ((tt_aentry_fp_in B RG HGSB) _ _ _ _ _ HEOK r Hr x Hx) as (q & n & Hq & Hqx).
  exact (KBL q n x ((tt_aentry_blks_in B RG HGSB) _ _ _ _ _ HEOK _ Hq) Hqx). }
split.
{ apply ((tt_asrc_clr B RG HGSB) ly1 S1 W1 m1 mF (dHA RG cx) h1 Hsrc).
  - intros x Hx N. apply KI; [clear - Hx HAr GS1 GS2; unfold ASRC in *; lia | exact N
    | intros Hy; clear - Hy Hx HAr TEG; unfold ASRC in *; lia].
  - intros q n x Hq Hqx. exact (KBL q n x ((tt_asrc_blks_in B RG HGSB) _ _ _ _ _ _ Hsrc _ Hq) Hqx).
  - exact HWK.
  - exact V12. }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KI;
      clear - Hx Hi Hne Hj4 GS1 GS2 TEG; unfold dHA, ASRC in *; lia.
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KI;
      clear - Hx Hi Hne Hj4 GS1 GS2 TEG; unfold dHA, ASRC in *; lia. }
split.
{ intros x Hx1 Hx2. apply (tt_abyte_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2)).
  apply KI; [clear - Hx1 GS1 GS2; unfold ASRC in *; lia | intros Hy; apply Hx2; clear - Hy; unfold ASRC; lia
  | intros Hy; clear - Hy Hx1 TEG; lia]. }
split.
{ pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AWERR & _).
  refine ((tt_aout_ev B RG HRGD HGSB) ly1 S1 W1 m1 mF _ _ _ _ _ _ 4 Hout _ _ VERR _ _).
  - intros r Hr x Hx Hne. destruct ((tt_aout_fp_in B RG HG HGO HRGD HGSB) _ _ r Hr x Hx) as [(Hi1 & Hi2 & _) | (q & n & Hq & Hqx)].
    + apply KI; [exact Hi1 | intros Hy; apply Hi2; clear - Hy HAr; lia | exact Hne].
    + exact (KBL q n x ((tt_aout_blks_in B RG HGSB) _ _ _ _ _ _ _ _ _ _ Hout _ Hq) Hqx).
  - intros Hc x Hx Hy.
    assert (Hin : In (out1, drain_b_c.ds_ocap sg) (ablocks B ly1 S1)).
    { apply ((tt_aout_blks_in B RG HGSB) _ _ _ _ _ _ _ _ _ _ Hout). unfold aout_blks.
      rewrite (proj2 (Z.eqb_neq _ 0) Hc). left. reflexivity. }
    apply (tt_blk_noimg_x _ _ _ _ _ _ _ _ x HAR Hin); [pose proof ((tt_req_ge RG) (drain_b_c.ds_ocap sg)); lia|].
    apply GIMG, ERG. exact Hy.
  - intros i Hi. apply HWK. exact (AWERR i Hi).
  - lia. }
split; [exact Hlivout | exact Hperm].
Qed.

Lemma tt_dmem_drb_xR : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF
  (data : list byte),
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
0 < re_cap e1 -> (length data <= length (re_junk e1))%nat ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
   ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
   ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
(forall i, (i < length data)%nat ->
   aview SEGS (w_H W1) mF (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)) ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 mF mdF k1 (tt_junk e1 (data ++ skipn (length data) (re_junk e1))) h1 sg out1
  ev1 sent LB1.
Proof.
intros cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF data HB HMEM HJF Hcp Hdl KEEP PRES CPY.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : ARx ly1 S1 hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx)
  by (unfold dsp0; clear - Hslo Hceil; change DRAIN_STK_x with 16976 in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
pose proof HGSB as (GS1 & GS2 & GS3).
pose proof HEOK as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
  HND1 & HND2 & Hkeys).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [clear - Hc0 Hcp; lia|].
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & _). rewrite RQC in Hbceil.
(* g_s's bytes are image bytes (HG) *)
assert (GSI : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> in_img SEGS x)
  by (intros x Hx; apply (proj1 (HG x ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia)))).
pose proof (Permutation_NoDup Hperm (tt_ablocks_nodup_x _ _ _ _ _ _ HAR)) as HNDp.
unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by lia. cbn [app] in HNDp.
apply List.NoDup_cons_iff in HNDp as [HGnot HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot _].
assert (HDL : Z.of_nat (length data) <= re_cap e1 - re_used e1) by (rewrite <- Hjl; lia).
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> (q, n) <> (re_buf e1, re_cap e1) -> q <= x < q + n ->
  abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hne Hx. destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof ((tt_req_ge RG) n) as Rq.
  pose proof (tt_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hin Hbin Hne) as Hap. rewrite RQC in Hap.
  split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; clear - Hx H4 Hc Rq Hap HspA C1 HUlen HDL; unfold tt_apart, DRAIN_FRAME, ESTACK in *; lia. }
(* an image byte is kept: the copy's bytes are the relay buffer's, a live block, off the image (blk_img_x) *)
assert (KI : forall x, in_img SEGS x -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. pose proof (pa_img_range _ Hx) as Hxr. split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP;
    [ clear - Hxr; lia
    | intros Hy; apply (tt_blk_noimg_x _ _ _ _ _ _ _ _ x HAR Hbin); [rewrite RQC; clear - Hy HUlen HDL; lia | exact Hx]
    | clear - Hxr HspA C1; unfold DRAIN_FRAME, ESTACK in *; lia .. ]. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME + 88 <= x < dsp0 cx - DRAIN_FRAME + 192 \/
  dsp0 cx - DRAIN_FRAME + 208 <= x < dsp0 cx -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; clear - Hx HspA HspB C1 Hbceil HUlen HDL; unfold DRAIN_FRAME, ESTACK in *; lia. }
assert (NB : forall b, In b (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> b <> (re_buf e1, re_cap e1))
  by (intros b Hb Heq; apply Hbufnot; rewrite <- Heq; exact Hb).
assert (INB : forall b, In b (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). right. unfold aentry_blks.
  rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by lia. cbn [app]. right. exact Hb. }
assert (KH : forall q n x, In (q, n) (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> q <= x < q + n ->
    abyte_kept W1 m1 W1 mF x)
  by (intros q n x Hb Hx; exact (KBL q n x (INB _ Hb) (NB _ Hb) Hx)).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept _ m1 mF x (PRES x) Hw)).
split; [exact HJF|].
split; [intros x Hx; rewrite (proj1 (KI x (tt_rom_img x Hx))); exact (Hrom x Hx)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply PRES; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & ASV).
  assert (HVM : forall o n v, 88 <= o -> (o + Z.of_nat n <= 192 \/ 208 <= o) -> o + Z.of_nat n <= DRAIN_FRAME ->
    val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o) n v -> val_mem SEGS (arm W1 mF) (dsp0 cx - DRAIN_FRAME + o) n v)
    by (intros o n v Ho1 Ho2 Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply KFR; lia | exact Hv]).
  repeat match goal with |- _ /\ _ => split end;
    try (apply HVM; [lia | cbn; lia | cbn; unfold DRAIN_FRAME; lia | assumption]).
  intros i Hi. specialize (ASV i Hi).
  replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i))
    in ASV |- * by lia.
  apply HVM; [lia | cbn; lia | cbn; unfold DRAIN_FRAME; lia | exact ASV]. }
split.
{ assert (G0 : garr8 SEGS (arm W1 mF) (dxSA cx) (bzs (entry_bytes e1))).
  { apply (tt_garr8_kept W1 m1 W1 mF _ _ Hgarr). intros x Hx. rewrite (tt_entry_len e1 Hpad1 Hpad2) in Hx.
    apply (proj1 (KBL (dxG cx) ATABLE x HGin1
      ltac:(intros X; injection X as X1 X2; clear - X2 Hcapr Hcp; unfold ATABLE in *; lia)
      ltac:(clear - Hx HGSA HSAG; unfold AENT, ATABLE in *; lia))). }
  exact G0. }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ unfold aentry_okx, tt_junk.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
  split; [exact Heof|]. split; [exact Hskip|]. split; [exact Hpad1|]. split; [exact Hpad2|].
  split; [exact Hfd|]. split; [exact Hcapr|]. split; [exact HUlen|]. split; [exact Husedc|].
  split.
  { right. split; [exact Hcpos|]. split; [exact Hbin|].
    split; [rewrite length_app, length_skipn; clear - Hjl Hdl; lia|].
    rewrite tt_bzs_app in Hbuf8. apply garr8_app in Hbuf8 as [GU GJ].
    rewrite !tt_bzs_app. apply garr8_app. split.
    - apply (tt_garr8_kept W1 m1 W1 mF _ _ GU). intros x Hx. rewrite tt_bzs_len in Hx.
      apply KEEP; clear - Hx HUlen HDL Hbceil Hb4096 HspA C1; unfold DRAIN_FRAME, ESTACK in *; lia.
    - rewrite tt_bzs_len. rewrite HUlen. apply garr8_app. split.
      + apply (tt_garr8_of_aview RG HGSB); [|apply (tt_bzs_range RG)].
        intros i Hi. rewrite tt_bzs_len in Hi. exact (CPY i Hi).
      + rewrite tt_bzs_len, HUlen in GJ.
        pose proof (tt_garr8_skipn _ _ _ (length data) GJ ltac:(rewrite tt_bzs_len; exact Hdl)) as GJ'.
        rewrite tt_skipn_bzs in GJ'. rewrite tt_bzs_len.
        apply (tt_garr8_kept W1 m1 W1 mF _ _ GJ'). intros x Hx. rewrite tt_bzs_len, length_skipn in Hx.
        apply KEEP; clear - Hx HUlen HDL Hbceil Hb4096 HspA C1 Hjl Hdl; unfold DRAIN_FRAME, ESTACK in *; lia. }
  split; [exact Hnheld|].
  split.
  { destruct Hheld as [H0 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H0 | right].
    split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx.
    apply (KH (re_hp e1) (re_kh e1)); [apply in_or_app; left; apply in_or_app; left;
      rewrite (proj2 (Z.eqb_neq _ 0) Hz); left; reflexivity|].
    unfold bzs in Hx. rewrite length_map, (tt_key_ptrs_len RG) in Hx. unfold re_nheld in Hk1. lia. }
  split; [exact HND1|]. split; [exact HND2|].
  rewrite Forall_forall in Hkeys |- *. intros k Hk. destruct (Hkeys k Hk) as (K1 & K2 & K3).
  split; [exact K1|]. split; [|exact K3].
  apply (akept_garr8 W1 m1); [|exact K2]. intros x Hx.
  apply (KH (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
  - apply in_or_app. left. apply in_or_app. right.
    exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hk).
  - unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia. }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 mF (dHA RG cx) h1 Hsrc); [|exact ((tt_asrc_blks_in B RG HGSB) _ _ _ _ _ _ Hsrc)].
  intros r Hr x Hx. destruct ((tt_asrc_fp_in B RG HGSB) _ _ _ _ _ _ Hsrc r Hr x Hx) as [X | (q & n & Hq & Hqx)].
  - apply KI, GSI. clear - X Hj4 GS1 GS2. unfold dHA, ASRC in *. lia.
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. left. exact Hq. }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KI, GSI.
    clear - Hx Hi GS1 GS2. unfold ASRC in *. lia.
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KI, GSI.
    clear - Hx Hi GS1 GS2. unfold ASRC in *. lia. }
split.
{ intros x Hx1 Hx2. apply (tt_abyte_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2)).
  apply KI, GSI. clear - Hx1. lia. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF); [exact Hout | |
    exact ((tt_aout_blks_in B RG HGSB) _ _ _ _ _ _ _ _ _ _ Hout)].
  intros r Hr x Hx. destruct (tt_aout_fp_img _ _ r Hr x Hx) as [Hi1 | (q & n & Hq & Hqx)].
  - exact (KI x Hi1).
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hq. }
split; [exact Hlivout | exact Hperm].
Qed.

Theorem dr_toptail_xR : dr_toptail_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_toptail_stmt_xR. intros cx hp kr sg D W1 c1 HB HT2 Kdi Kend Krb.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HT2 as (regs1 & ly1 & S1 & hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24 & R10 & R13 &
  HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
pose proof HFR as HFR'. unfold dr_frame in HFR'. cbv zeta in HFR'.
destruct HFR' as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSA0 & HGin0 & HGSA & HSAG & _ & _ & _ & Hj4 & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
pose proof Hafn as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
fold (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx) by (clear - Hslo Hceil HDS; rewrite HDS in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (HAR : ARx ly1 S1 hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HGin1) as (_ & HG4096 & HGceil & HGapp & _).
rewrite RQT in HGceil, HGapp.
pose proof HGSB as (GS1 & GS2 & GS3).
set (j := dxj cx) in *. set (GS := rg_s RG) in *. set (SA := dxSA cx) in *.
assert (HHA : dHA RG cx = GS + 96 * Z.of_nat j) by (unfold dHA, ASRC; reflexivity).
pose proof Hsrc as (V0 & V4 & V8 & V12 & HAWS & Hcl01 & Hei01 & Hopen & Hfdr & HPEND & V32 & V40 & V48 & V56 &
  Hrecs & Hnpart & Hovl & Hpin & Hpjl & Hpg & HnoW & HEXP & HHELD & HNDB).
pose proof HPEND as (P0 & P8 & P12 & PAW & Pn & Pv & PND & Pnv & Precs).
rewrite HHA in R23, V0, V4, V8, V12, HAWS, V32, V40, V48, V56, P0, P8, P12, PAW.
replace (dHA RG cx) with (GS + 96 * Z.of_nat j) in * by (symmetry; exact HHA).
replace (GS + 96 * Z.of_nat j + 16 + 8) with (GS + 96 * Z.of_nat j + 24) in P8 by lia.
replace (GS + 96 * Z.of_nat j + 16 + 12) with (GS + 96 * Z.of_nat j + 28) in P12 by lia.
set (HA := GS + 96 * Z.of_nat j) in *.
set (ei := hs_eintr h1) in *. set (nn := hl_n (hs_pending h1)) in *. set (vv := hl_v (hs_pending h1)) in *.
set (off := hs_off h1) in *.
set (s0 := fst (tt_hd (hs_pending h1))). set (l0 := Z.of_nat (length (snd (tt_hd (hs_pending h1))))).
set (dn := dnum sg).
assert (Hj4' : 0 <= Z.of_nat j < 4) by lia.
assert (Hnn : 0 <= nn <= 2 ^ 30) by (unfold nn, hl_n in *; lia).
assert (Hvv : 0 <= vv < 2 ^ 64).
{ destruct Pv as [(_ & Hv0) | (Hcp & Hin & _)]; [rewrite Hv0; lia|].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof ((tt_req_ge RG) (AREC * hl_cap (hs_pending h1))). unfold AREC in *. lia. }
assert (Hoff : 0 <= off < 2 ^ 64).
{ destruct Hrecs as [(_ & ->) | (r & rs & Er & Ho1 & Ho2)]; [lia|].
  rewrite Forall_forall in Precs. destruct (Precs r ltac:(rewrite Er; left; reflexivity)) as (Hin & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _). pose proof ((tt_req_ge RG) (Z.of_nat (length (snd r)) + 1)). lia. }
pose proof ((tt_entry RG HGSB) W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) SA HA ei nn vv off s0 l0 dn Hsp
  ltac:(unfold DRAIN_FRAME; lia) ltac:(unfold DRAIN_FRAME; lia) ltac:(unfold DRAIN_FRAME; rewrite Zminus_mod, Hal16; reflexivity)
  R18 R21 R22 R23 ltac:(unfold AENT, ATABLE in *; lia) ltac:(unfold TT_HI, AENT, ATABLE in *; lia)
  ltac:(unfold HA; lia) ltac:(unfold HA, ASRC in *; lia) ltac:(unfold HA; rewrite Z.add_mod, GS3 by lia;
    replace (96 * Z.of_nat j) with ((12 * Z.of_nat j) * 8) by lia; rewrite Z.mod_mul by lia; reflexivity)
  ltac:(unfold ei in *; lia) Hnn Hvv Hoff F104 F112 F120 F136 F144 F152 F160 F168 F176 V12 P0 P8 V32) as HS.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
remember (Eimg (Ereg regs1 (tt_extra ei nn vv off s0 l0 dn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (k : nat) (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ k r Hr)).
assert (EX : forall i, (i < 7)%nat -> ew E (32 + i) = nth i (tt_extra ei nn vv off s0 l0 dn) (Z_to_bv 64 0))
  by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
assert (E18 : ew E 18 = Z_to_bv 64 GS) by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 SA) by (rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); exact R22).
assert (E23 : ew E 23 = Z_to_bv 64 HA) by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat j))
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (E32 : ew E 32 = Z_to_bv 64 ei) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 nn) by exact (EX 1%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (HAr : GS <= HA /\ HA + 96 <= GS + 4 * ASRC) by (unfold HA, ASRC; clear - Hj4'; lia).
assert (SHOK : sh_ok SEGS (SOff 21 0) TT_SH0 E (mrestrict (w_H W1) m1)).
{ unfold sh_ok, TT_SH0. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E (SOff 21 0) 23 GS (4 * ASRC) HA 0 96).
  - exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 m1 md1 GS (4 * ASRC) HAR HGSZ).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - apply (U_atom E 23 HA E23). unfold ASRC in *. lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF, ASRC in *. lia. }
(* ---- 0x83314 .. 0x8331c: the shadow address of &g_s[j].eintr, re-expressed ---- *)
paj_run_to_tok_xR RUNTOR HS HJ SHOK TTspan A_tt_sh1. { apply awr_ok_x_of0. awr_ok_tac. }
rename HFr into FR1; rename HG0 into GR1; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msA end.
tt_reg HS (14%bv : bv 5) X14.
assert (D14 : getr (ms_regs (restrict (w_H W1) msA)) 14%bv = sv_denot E (tt_shA 23 12)).
{ cbn [ms_regs restrict]. rewrite X14. apply ((tt_den_resh RG HGSB) E GS (Z.of_nat j) 12 E18 E24 E23 E21); unfold ASRC in *; lia. }
pose proof (tt_reseat E _ _ 14%bv _ HS D14 eq_refl) as HS'. clear HS D14 X14. rename HS' into HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
(* ---- 0x8331c .. 0x8332c: the shadow check folds; the test of g_s[j].eintr ---- *)
paj_run_tok_xR RUNR HS HJ SHOK TTspan. { apply awr_ok_x_of0. awr_ok_tac. }
rename HFr into FR2; rename HG0 into GR2; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
(* the two runs store nothing: every view kept, presence grown *)
assert (KALL2 : forall x, aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) m1 x).
{ intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msA) (ms_mem msB) x)
    by (apply FR2; apply (tt_nowr RG HGSB); vm_compute; reflexivity).
  apply (aview_eq_of SEGS (w_H W1) m1 (ms_mem msA) x). apply FR1; apply (tt_nowr RG HGSB); vm_compute; reflexivity. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msB) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hp))).
assert (U23 : bv_unsigned (ew E 23) = HA) by (rewrite E23; apply unsigned_lit_small; unfold ASRC in *; lia).
psrr_branch_tok RUN BRR HS SHOK TTspan.
- (* g_s[j].eintr == 0: the empty-pending test *)
  rewrite branch_eq_U, (U_atom E 32 ei E32), (U_lit E 0) in Hc by (unfold ei in *; lia).
  apply Z.eqb_eq in Hc. rename Hc into Hei0.
  paj_run_to_tok_xR RUNTOR HS HJ SHOK TTspan A_tt_sh2. { apply awr_ok_x_of0. awr_ok_tac. }
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msC end.
  tt_reg HS (15%bv : bv 5) X15.
  assert (D15 : getr (ms_regs (restrict (w_H W1) msC)) 15%bv = sv_denot E (tt_shA 23 24)).
  { cbn [ms_regs restrict]. rewrite X15. apply ((tt_den_resh RG HGSB) E GS (Z.of_nat j) 24 E18 E24 E23 E21); unfold ASRC in *; lia. }
  pose proof (tt_reseat E _ _ 15%bv _ HS D15 eq_refl) as HS'. clear HS D15 X15. rename HS' into HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
  (* ---- 0x8336c .. 0x8337c: the shadow check folds; the test of g_s[j].pending.n ---- *)
  paj_run_tok_xR RUNR HS HJ SHOK TTspan. { apply awr_ok_x_of0. awr_ok_tac. }
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msD end.
  assert (KALL4 : forall x, aview SEGS (w_H W1) (ms_mem msD) x = aview SEGS (w_H W1) m1 x).
  { intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msC) (ms_mem msD) x)
      by (apply FR4; apply (tt_nowr RG HGSB); vm_compute; reflexivity).
    rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msB) (ms_mem msC) x)
      by (apply FR3; apply (tt_nowr RG HGSB); vm_compute; reflexivity).
    exact (KALL2 x). }
  assert (PRES4 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msD) x)
    by (intros x Hp; exact (apresent_grows _ _ _ _ GR4 (apresent_grows _ _ _ _ GR3 (PRES2 x Hp)))).
  psrr_branch_tok RUN BRR HS SHOK TTspan.
  + (* g_s[j].pending.n == 0: DEND *)
    rewrite branch_eq_U, (U_atom E 33 nn E33), (U_lit E 0) in Hc by lia.
    apply Z.eqb_eq in Hc. rename Hc into Hn0.
    paj_run_to_tok_xR RUNTOR HS HJ SHOK TTspan A_dr_end. { apply awr_ok_x_of0. awr_ok_tac. }
    rename HFr into FR5; rename HG0 into GR5; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
    assert (KALLF : forall x, aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
    { intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msD) (ms_mem msF) x)
        by (apply FR5; apply (tt_nowr RG HGSB); vm_compute; reflexivity).
      exact (KALL4 x). }
    assert (PRESF : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR5 (PRES4 x Hp))).
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
    prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
    pose proof (tt_DMEM_kept_xR cx hp ly1 S1 hp1 W1 m1 (ms_mem msF) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KALLF PRESF) as HMEMF.
    pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
    match goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
    apply (Kend W1). unfold DEND_xR.
    exists (ms_regs msF), ly1, S1, hp1, (ms_mem msF), mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [unfold cfg_at; reflexivity|].
    split; [unfold spZ; rewrite P2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite P3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite P4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite P22, E22; reflexivity|].
    split; [rewrite P18, E18; reflexivity|].
    split; [rewrite P21, E21; reflexivity|].
    split; [rewrite P23, E23; reflexivity|].
    split; [rewrite P24, E24; reflexivity|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 HMEMF)))))|].
    split; [exact HMEMF|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|].
    split.
    { rewrite <- Lpend. unfold nn, hl_n in Hn0. destruct (hl_recs (hs_pending h1)); [reflexivity | cbn in Hn0; lia]. }
    split; [unfold ei in Hei0; rewrite Hei0 in Lei; destruct (drain_b_c.ds_eintr sg); [discriminate | reflexivity]|].
    split; [exact Hroom|]. split; [exact Hlater | exact Hbud].
  + (* g_s[j].pending.n <> 0: the data round *)
    rewrite branch_eq_U, (U_atom E 33 nn E33), (U_lit E 0) in Hc by lia.
    apply Z.eqb_neq in Hc. rename Hc into Hn0.
    destruct Hrecs as [(Hnil & _) | (r0 & rs0 & Erecs & Hoff0 & HoffL)].
    { exfalso. apply Hn0. unfold nn, hl_n. rewrite Hnil. reflexivity. }
    assert (Hs0 : s0 = fst r0) by (unfold s0, tt_hd; rewrite Erecs; reflexivity).
    assert (Hl0 : l0 = Z.of_nat (length (snd r0))) by (unfold l0, tt_hd; rewrite Erecs; reflexivity).
    pose proof Precs as Precs'. rewrite Forall_forall in Precs'.
    destruct (Precs' r0 ltac:(rewrite Erecs; left; reflexivity)) as (Hr0in & Hr0g & _ & Hr0len).
    specialize (Hr0len eq_refl). clear Precs'.
    destruct Pv as [(Hcap0 & _) | (Hcpv & Hvin & Hjv & Hvg)].
    { exfalso. clear - Pn Hcap0 Hn0 Hnn. lia. }
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hr0in) as (_ & Hs4096 & Hsceil & Hsapp & _).
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hvin) as (_ & Hv4096 & Hvceil & Hvapp & _).
    pose proof ((tt_req_ge RG) (Z.of_nat (length (snd r0)) + 1)) as Rq0.
    pose proof ((tt_req_ge RG) (AREC * hl_cap (hs_pending h1))) as Rqv.
    pose proof (tt_blk_gs_x _ _ _ _ _ _ _ _ HA 96 HAR Hvin (proj1 HAr) (proj2 HAr) ltac:(tt_num)) as Hvgs.
    rewrite Erecs in Hvg.
    destruct ((tt_vec_rec RG HGSB) W1 m1 vv r0 rs0 _ Hvg ltac:(clear - Hs4096 Hsceil Rq0 C1; lia)
      ltac:(clear - Hsceil Rq0 C1 Hs4096; lia)) as (VR0 & VR8).
    pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
      HND1 & HND2 & Hkeys).
    pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
    assert (HUL : ulen sg = re_used e1) by (unfold ulen; rewrite <- Lu, tt_bzs_len; exact HUlen).
    assert (Hcp4 : 4096 + re_used e1 <= re_cap e1) by (clear - Hroom HUL Lcap; rewrite HUL, <- Lcap in Hroom; lia).
    destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [exfalso; clear - Hc0 Hcp4 HUlen; lia|].
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
    assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
    assert (Hpend0 : drain_b_c.ds_pend sg = bzs (snd r0) :: map (fun r => bzs (snd r)) rs0)
      by (rewrite <- Lpend, Erecs; reflexivity).
    assert (Hdn : dn = Z.min (l0 - off) (re_cap e1 - re_used e1)).
    { unfold dn, dnum, dhead. rewrite Hpend0, tt_bzs_len, <- Hl0, <- Loff, <- Lcap, HUL. reflexivity. }
    assert (Hcapb : re_cap e1 <= 16384) by (clear - Hcapr; lia).
    assert (Hdnr : 1 <= dn <= 16384) by (clear - Hdn Hoff0 HoffL Hl0 Hcp4 Hcapb HUlen; rewrite Hdn; lia).
    (* ---- 0x8337c .. 0x83388: the shadow address of &g_s[j].pending, re-expressed before its store ---- *)
    paj_run_to_tok_xR RUNTOR HS HJ SHOK TTspan A_tt_sh3. { apply awr_ok_x_of0. awr_ok_tac. }
    rename HFr into FR5; rename HG0 into GR5; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msE end.
    assert (KALL5 : forall x, aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
    { intros x. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem msD) (ms_mem msE) x)
        by (apply FR5; apply (tt_nowr RG HGSB); vm_compute; reflexivity). exact (KALL4 x). }
    assert (PRES5 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msE) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR5 (PRES4 x Hp))).
    tt_reg HS (11%bv : bv 5) X11.
    assert (D11 : getr (ms_regs (restrict (w_H W1) msE)) 11%bv = sv_denot E (tt_shA 23 16)).
    { cbn [ms_regs restrict]. rewrite X11.
      apply ((tt_den_resh RG HGSB) E GS (Z.of_nat j) 16 E18 E24 E23 E21); clear - GS1 GS2 Hj4'; unfold ASRC in *; lia. }
    pose proof (tt_reseat E _ _ 11%bv _ HS D11 eq_refl) as HS'. clear HS D11 X11. rename HS' into HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
    (* the vector's record, the frame slots the round stores, and the atom facts of the round *)
    assert (E34 : ew E 34 = Z_to_bv 64 vv) by exact (EX 2%nat ltac:(lia)).
    assert (E35 : ew E 35 = Z_to_bv 64 off) by exact (EX 3%nat ltac:(lia)).
    assert (E36 : ew E 36 = Z_to_bv 64 s0) by exact (EX 4%nat ltac:(lia)).
    assert (E37 : ew E 37 = Z_to_bv 64 l0) by exact (EX 5%nat ltac:(lia)).
    assert (E38 : ew E 38 = Z_to_bv 64 dn) by exact (EX 6%nat ltac:(lia)).
    assert (Hvvb : 4096 <= vv /\ vv + 16 <= TT_HI)
      by (clear - Hv4096 Hvceil Rqv C1 Hcpv; unfold TT_HI, AREC in *; lia).
    assert (Hs0b : 4096 <= s0 /\ s0 + l0 < TT_HI)
      by (rewrite Hs0, Hl0; clear - Hs4096 Hsceil Rq0 C1; unfold TT_HI in *; lia).
    assert (Hvva : vv + 16 <= alloc_ceiling) by (clear - Hvceil Rqv Hcpv; unfold AREC in *; lia).
    assert (Hs0a : s0 + l0 + 1 <= alloc_ceiling) by (rewrite Hs0, Hl0; clear - Hsceil Rq0; lia).
    assert (Hl0b : 1 <= l0) by (rewrite Hl0; clear - Hr0len; lia).
    assert (Uvv : bv_unsigned (ew E 34) = vv) by (rewrite E34; apply unsigned_lit_small; clear - Hvvb; unfold TT_HI in *; lia).
    assert (U35 : bv_unsigned (ew E 35) = off) by (rewrite E35; apply unsigned_lit_small; clear - Hoff; lia).
    assert (U36 : bv_unsigned (ew E 36) = s0) by (rewrite E36; apply unsigned_lit_small; clear - Hs0b; unfold TT_HI in *; lia).
    assert (U37 : bv_unsigned (ew E 37) = l0) by (rewrite E37; apply unsigned_lit_small; clear - Hs0b Hl0b; unfold TT_HI in *; lia).
    assert (U38 : bv_unsigned (ew E 38) = dn) by (rewrite E38; apply unsigned_lit_small; clear - Hdnr; lia).
    apply (st_ok_pi_add_fact _ _ _ 34%nat (mkAF 4096 TT_HI 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Uvv, Z.pow_0_r, Z.mod_1_r; clear - Hvvb; lia].
    apply (st_ok_pi_add_fact _ _ _ 36%nat (mkAF 4096 TT_HI 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U36, Z.pow_0_r, Z.mod_1_r; clear - Hs0b Hl0b; lia].
    apply (st_ok_pi_add_fact _ _ _ 37%nat (mkAF 1 TT_HI 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U37, Z.pow_0_r, Z.mod_1_r; clear - Hs0b Hl0b; lia].
    apply (st_ok_pi_add_fact _ _ _ 38%nat (mkAF 1 16384 0)) in HS;
      [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U38, Z.pow_0_r, Z.mod_1_r; clear - Hdnr; lia].
    apply (st_ok_pi_add_region _ _ _ tt_vec) in HS;
      [ | vm_compute; reflexivity
        | unfold region_ok, tt_vec;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite Uvv; split; [clear - Hvvb; lia|]; split; [clear - Hvvb; unfold TT_HI in *; lia|];
          split; [intros o Ho; lia|];
          repeat apply Forall_cons; try apply Forall_nil;
          [ apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 36 0) s0);
            [ exact (den_atom0 E 36 s0 E36 ltac:(clear - Hs0b; unfold TT_HI in *; lia)) | zside | zside
            | rewrite Z.add_0_r; apply (tt_vm_kept W1 m1); [intros k Hk; apply KALL5 | rewrite Hs0; exact VR0] ]
          | apply (chunk_ok_val SEGS E _ _ 8 8 (SOff 37 0) l0);
            [ exact (den_atom0 E 37 l0 E37 ltac:(clear - Hs0b Hl0b; unfold TT_HI in *; lia)) | zside | zside
            | apply (tt_vm_kept W1 m1); [intros k Hk; apply KALL5 | rewrite Hl0; exact VR8] ] ]
        | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
          apply all_disjoint_of_extents; unfold extent_of_region, tt_vec;
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uvv, Usp, U23;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
          split; [clear - Hvva HspA; unfold DRAIN_FRAME in *; lia|];
          split; [clear - Hvgs Rqv Hcpv; unfold tt_apart, AREC in *; lia | exact I] ].
    assert (SWR : forall o, 24 <= o < 208 -> writable_at SEGS (arm W1 (ms_mem msE)) (dsp0 cx - DRAIN_FRAME + o)).
    { pose proof HJ as (_ & _ & (memS & HJi & _) & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. rewrite HDS. unfold DRAIN_FRAME. lia. }
    apply (st_ok_pi_add_region _ _ _ tt_f0) in HS;
      [ | vm_compute; reflexivity
        | unfold region_ok, tt_f0;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite Usp; split; [clear - HspA C1; unfold DRAIN_FRAME in *; lia|];
          split; [clear - HspB; unfold DRAIN_FRAME in *; lia|]; split; [intros o Ho; apply SWR; lia | apply Forall_nil]
        | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
          apply all_disjoint_of_extents; unfold extent_of_region, tt_f0;
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uvv, Usp, U23;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
          split; [clear - Hvva HspA; unfold DRAIN_FRAME in *; lia|];
          split; [lia|];
          split; [clear - HspA HAr GS2 C1; unfold DRAIN_FRAME, ASRC in *; lia | exact I] ].
    apply (st_ok_pi_add_region _ _ _ tt_f2) in HS;
      [ | vm_compute; reflexivity
        | unfold region_ok, tt_f2;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite Usp; split; [clear - HspA C1; unfold DRAIN_FRAME in *; lia|];
          split; [clear - HspB; unfold DRAIN_FRAME in *; lia|]; split; [intros o Ho; apply SWR; lia | apply Forall_nil]
        | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
          apply all_disjoint_of_extents; unfold extent_of_region, tt_f2;
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uvv, Usp, U23;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
          split; [lia|];
          split; [clear - Hvva HspA; unfold DRAIN_FRAME in *; lia|];
          split; [lia|];
          split; [clear - HspA HAr GS2 C1; unfold DRAIN_FRAME, ASRC in *; lia | exact I] ].
    assert (HARE : ARx ly1 S1 hp1 W1 (ms_mem msE) (with_vm_backing (m_vm_lazy _) _ _))
      by (eapply ajournal_gx_AR_xR; exact HJ).
    assert (SHOK2 : sh_ok SEGS (SOff 21 0) TT_SHD E (mrestrict (w_H W1) (ms_mem msE))).
    { unfold sh_ok, TT_SHD. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply (shent_ok_of_range SEGS (w_H W1) (ms_mem msE) E (SOff 21 0) 23 GS (4 * ASRC) HA 0 96).
        + exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 (ms_mem msE) _ GS (4 * ASRC) HARE HGSZ).
        + exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
        + apply (U_atom E 23 HA E23). clear - HAr GS1 GS2. unfold ASRC in *. lia.
        + clear - HAr. lia.
        + clear - HAr. lia.
        + intros x Hx. clear - Hx HAr GS1 GS2. unfold SHADOW_OFF, ASRC in *. lia.
      - apply (shent_ok_of_range SEGS (w_H W1) (ms_mem msE) E (SOff 21 0) 34 vv (AREC * hl_cap (hs_pending h1)) vv 0 16).
        + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msE) _ vv
            (AREC * hl_cap (hs_pending h1)) vv (AREC * hl_cap (hs_pending h1)) HARE Hvin); [lia | clear - Rqv; lia].
        + exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
        + apply (U_atom E 34 vv E34). clear - Hvvb. unfold TT_HI in *. lia.
        + lia.
        + clear - Hcpv. unfold AREC. lia.
        + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
          clear - Hx Hvapp Hvva Rqv Hcpv C1. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AREC in *. lia. }
    (* ---- 0x83388 .. 0x833b4: shadow(&pending) at 80(sp), v[0].n's shadow check, shadow(&pending_off) ---- *)
    paj_run_to_tok_xR RUNTOR HS HJ SHOK2 TTspan A_tt_sh4.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      apply awr_ok_x_cons.
      { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
        left. split; [left; rewrite HDS; unfold DRAIN_FRAME in *; lia | lia]. }
      apply awr_ok_x_cons.
      { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
        left. split; [left; rewrite HDS; unfold DRAIN_FRAME in *; lia | lia]. }
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    rename HFr into FR6; rename HG0 into GR6; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msG end.
    tt_reg HS (14%bv : bv 5) X14b.
    assert (D14b : getr (ms_regs (restrict (w_H W1) msG)) 14%bv = sv_denot E (tt_shA 23 32)).
    { cbn [ms_regs restrict]. rewrite X14b.
      apply ((tt_den_resh RG HGSB) E GS (Z.of_nat j) 32 E18 E24 E23 E21); clear - GS1 GS2 Hj4'; unfold ASRC in *; lia. }
    pose proof (tt_reseat E _ _ 14%bv _ HS D14b eq_refl) as HS'. clear HS D14b X14b. rename HS' into HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
    (* ---- 0x833b4 .. 0x833cc: n = v[0].n - pending_off, compared with cap - used ---- *)
    paj_run_tok_xR RUNR HS HJ SHOK2 TTspan. { tt_awr_regions Usp HDS. }
    rename HFr into FR7; rename HG0 into GR7; clear HF.
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msH end.
    assert (E13 : ew E 13 = Z_to_bv 64 (re_cap e1 - re_used e1))
      by (rewrite (EREG 13%nat 13%bv) by (first [lia | reflexivity]); exact R13).
    assert (U13 : bv_unsigned (ew E 13) = re_cap e1 - re_used e1)
      by (rewrite E13; apply unsigned_lit_small; clear - Hcp4 Hcapb HUlen; lia).
    assert (UC7 : U E (SAlu ALU_ADD (SMd M_MUL (SOff 35 0) (SLit (-1))) (SOff 37 0)) = l0 - off)
      by (apply ((tt_U_sub RG HGSB) E 35 37 off l0 U35 U37); clear - Hoff0 HoffL Hl0 Hs0b; unfold TT_HI in *; lia).
    assert (Hcu : 0 <= re_cap e1 - re_used e1 < 2 ^ 64) by (clear - Hcp4 Hcapb HUlen; lia).
    (* the views kept so far: the round stored only into the frame slots [24, 88) and [192, 208) *)
    assert (KALLH : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msH) x = aview SEGS (w_H W1) m1 x).
    { intros x Hx N1 N2.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msG) (ms_mem msH) FR7 x Hx)
        by (apply ((tt_nowr_fr RG HGSB) E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]).
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msE) (ms_mem msG) FR6 x Hx)
        by (apply ((tt_nowr_fr RG HGSB) E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]).
      exact (KALL5 x). }
    assert (PRESH : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msH) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR7 (apresent_grows _ _ _ _ GR6 (PRES5 x Hp)))).
    clear FR6 FR7 GR6 GR7.
    (* both arms of n = min(...) reach 0x833d4 in the same state (s4 = n, the arm's condition dropped):
       the rest of the round is proved once, as CONT *)
    eassert (CONT : forall (mdx : _) (ms : _), st_ok_pi SEGS VAL E ?[SSN] (restrict (w_H W1) ms) ->
      @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx)
        (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 (ms_mem ms) mdx k1 ->
      sh_ok SEGS (SOff 21 0) TT_SHD E (mrestrict (w_H W1) (ms_mem ms)) ->
      (forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
        ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
        aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x) ->
      (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x) ->
      SRrG SEGS R W1 (mkCfg ms mdx) (dPOST_xR B PST ARx MT RP RG R cx hp kr)).
    2: {
    psrr_branch_tok RUN BRR HS SHOK2 TTspan;
      [ rewrite branch_ltu_U, UC7, (U_atom E 13 (re_cap e1 - re_used e1) E13 Hcu) in Hc;
        apply Z.ltb_lt in Hc;
        assert (Hdn' : dn = l0 - off) by (clear - Hdn Hc; lia);
        paj_run_to_tok_xR RUNTOR HS HJ SHOK2 TTspan A_tt_n; [tt_awr_regions Usp HDS|];
        rename HFr into FR8; rename HG0 into GR8; clear HF;
        match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msI end;
        tt_reg HS (20%bv : bv 5) X20;
        assert (D20 : getr (ms_regs (restrict (w_H W1) msI)) 20%bv = sv_denot E (SOff 38 0))
          by (cbn [ms_regs restrict]; rewrite X20, (den_atom0 E 38 dn E38) by (clear - Hdnr; lia);
              rewrite (denot_lit_U E (SAlu ALU_ADD (SMd M_MUL (SOff 35 0) (SLit (-1))) (SOff 37 0))), UC7, Hdn';
              reflexivity)
      | rewrite branch_ltu_U, UC7, (U_atom E 13 (re_cap e1 - re_used e1) E13 Hcu) in Hc;
        apply Z.ltb_ge in Hc;
        assert (Hdn' : dn = re_cap e1 - re_used e1) by (clear - Hdn Hc; lia);
        paj_run_to_tok_xR RUNTOR HS HJ SHOK2 TTspan A_tt_n; [tt_awr_regions Usp HDS|];
        rename HFr into FR8; rename HG0 into GR8; clear HF;
        match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msI end;
        tt_reg HS (20%bv : bv 5) X20;
        assert (D20 : getr (ms_regs (restrict (w_H W1) msI)) 20%bv = sv_denot E (SOff 38 0))
          by (cbn [ms_regs restrict]; rewrite X20, (den_atom0 E 38 dn E38) by (clear - Hdnr; lia);
              rewrite (den_atom0 E 13 (re_cap e1 - re_used e1) E13 Hcu), Hdn'; reflexivity) ].
    all: pose proof (tt_reseat E _ _ 20%bv _ HS D20 eq_refl) as HS'; clear HS D20 X20; rename HS' into HS.
    all: pose proof (st_ok_pi_facts_incl E _ _ _ _ HS (fun x Hx => Hx) (fun x Hx => Hx)) as HS'; clear HS;
      rename HS' into HS.
    all: match type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
    all: assert (KALLI : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msI) x = aview SEGS (w_H W1) m1 x)
      by (intros x Hx N1 N2;
          rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msH) (ms_mem msI) FR8 x Hx)
            by (apply ((tt_nowr_fr RG HGSB) E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]);
          exact (KALLH x Hx N1 N2)).
    all: exact (CONT _ _ HS HJ SHOK2 KALLI (fun x Hp => apresent_grows _ _ _ _ GR8 (PRESH x Hp))). }
    intros mdx msI HSc HJc SHc KALLc PRESc. clear HS HJ SHOK2 KALLH PRESH.
    rename HSc into HS, HJc into HJ, SHc into SHOK2.
    (* ---- 0x833d4 .. 0x833f4: shadow(&pending) at 40(sp), v[0].s's shadow check, the jal to __asan_memcpy ---- *)
    paj_run_tok_xR RUNR HS HJ SHOK2 TTspan; [tt_awr_regions Usp HDS|].
    rename HFr into FR9; rename HG0 into GR9; clear HF.
    match type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into msM end.
    assert (KALLM : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msM) x = aview SEGS (w_H W1) m1 x).
    { intros x Hx N1 N2.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msI) (ms_mem msM) FR9 x Hx)
        by (apply ((tt_nowr_fr RG HGSB) E _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact Usp | exact N1 | exact N2]).
      exact (KALLc x Hx N1 N2). }
    assert (PRESM : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msM) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR9 (PRESc x Hp))).
    clear FR9 GR9 KALLc PRESc.
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. tt_reg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    assert (Usp2 : spZ (ms_regs msM) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Usp).
    pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARM.
    (* the relay's buffer is not the vector's block nor the head text's block *)
    pose proof (Permutation_NoDup Hperm (tt_ablocks_nodup_x _ _ _ _ _ _ HAR)) as HNDp.
    unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by (clear - Hcpos; lia).
    cbn [app] in HNDp.
    apply List.NoDup_cons_iff in HNDp as [_ HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot _].
    assert (Hvne : (vv, AREC * hl_cap (hs_pending h1)) <> (re_buf e1, re_cap e1)).
    { intros X. apply Hbufnot. rewrite <- X. apply in_or_app. right. apply in_or_app. left.
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks.
      destruct (Z.eqb_spec (hl_cap (hs_pending h1)) 0) as [Hc0|Hc0]; [clear - Hc0 Hcpv; lia|].
      cbn [app]. left. reflexivity. }
    assert (Htne : (fst r0, Z.of_nat (length (snd r0)) + 1) <> (re_buf e1, re_cap e1)).
    { intros X. apply Hbufnot. rewrite <- X. apply in_or_app. right. apply in_or_app. left.
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks.
      destruct (Z.eqb_spec (hl_cap (hs_pending h1)) 0) as [Hc0|Hc0]; [clear - Hc0 Hcpv; lia|].
      cbn [app]. right. rewrite Erecs. cbn [map]. left. reflexivity. }
    pose proof (tt_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hr0in Hbin Htne) as Htap. rewrite RQC in Htap.
    pose proof (tt_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hvin Hbin Hvne) as Hvap. rewrite RQC in Hvap.
    pose proof (tt_blk_gs_x _ _ _ _ _ _ _ _ HA 96 HAR Hbin (proj1 HAr) (proj2 HAr) ltac:(tt_num)) as Hbgs.
    rewrite RQC in Hbgs.
    assert (Hdnl : off + dn <= l0) by (clear - Hdn Hoff0; rewrite Hdn; lia).
    assert (Hdnc : dn <= re_cap e1 - re_used e1) by (clear - Hdn; rewrite Hdn; lia).
    rewrite RQC in Hbceil.
    destruct HJ as (HSTK2 & HXO2 & (memS2 & HJi2 & HAG2) & HOUT2). rewrite !Z.add_0_r in HJi2.
    (* __asan_memcpy(s->buf + s->used, v[0].s + pending_off, n) *)
    eapply (SRrG_bind SEGS R R_trans).
    { eapply (aj_intrin_at_xR B PST ARx LAWS R_trans WLE_R OCpy (SIGMA WS_asan_memcpy) AMEMCPY W1 (ms_regs msM) (ms_mem msM)
        DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx) memS2 (dxmd cx) [] ly1 S1 hp1 _ k1
        (re_buf e1 + re_used e1) (s0 + off) dn (- DRAIN_FRAME) _ HJi2).
      - rewrite Q10, (EREG 10%nat 10%bv) by tt_num. exact R10.
      - rewrite Q11, denot_lit_U, U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E 35 off E35), (U_atom E 36 s0 E36) by (clear - Hoff Hs0b; unfold TT_HI in *; lia).
        rewrite zcanon_id by (unfold M64; clear - Hs0b Hoff0 HoffL Hl0; unfold TT_HI in *; lia).
        unfold w64. f_equal. ring.
      - rewrite Q12, E38. reflexivity.
      - clear - Hdnr. lia.
      - clear - Hb4096 HUlen. lia.
      - clear - Hbceil Hdnc C1. lia.
      - rewrite Usp2. ring.
      - unfold DRAIN_FRAME. reflexivity.
      - tt_num.
      - tt_num.
      - rewrite Q3, (EREG 3%nat 3%bv), R3 by tt_num. exact Hgp0.
      - rewrite Q4, (EREG 4%nat 4%bv), R4 by tt_num. exact Htp0.
      - exact Q1.
      - apply ret_ok_codeptr_v; [tt_num | reflexivity].
      - intros a Ha. split; [|clear - Ha Hbceil Hdnc HspA; unfold ESTACK, DRAIN_FRAME; lia].
        assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
        destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
        + right. left. split.
          * apply (Permutation_in _ HPERM0) in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|Hin0];
              [injection X as X1 X2; clear - X2 Hcp4 HUlen; unfold ATABLE, AENT in *; lia|].
            assert (Hin3 : In (re_buf e1, re_cap e1)
              (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
            { apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
              apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
              apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; right; exact X|].
              exfalso. apply Hbufnot. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
              exact Hin0. }
            unfold dFP, dr_fp. apply inFP_cons. right. exists (re_buf e1, re_buf e1 + req_size (re_cap e1)).
            split; [unfold ablocks_fp; exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ Hin3)|].
            cbn [fst snd]. rewrite RQC. clear - Ha Hdnc HUlen. lia.
          * exists (re_buf e1), (re_cap e1). split; [exact Hbin | rewrite RQC; clear - Ha Hdnc HUlen; lia].
        + right. right. left. exists (re_buf e1), (re_cap e1). split; [exact Hbin|].
          split; [exact Hnot0 | rewrite RQC; clear - Ha Hdnc HUlen; lia].
      - apply (tt_amem_range_blk_x _ _ _ _ _ _ _ _ _ _ HARM Hbin); [clear - HUlen; lia | clear - Hdnr; lia
        | rewrite RQC; clear - Hdnc; lia].
      - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (re_buf e1) (re_cap e1)
          (re_buf e1 + re_used e1) dn HARM Hbin); [clear - HUlen; lia | rewrite RQC; clear - Hdnc; lia].
      - intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (re_buf e1)
          (re_cap e1) (re_buf e1 + re_used e1) dn HARM Hbin); [clear - HUlen; lia | rewrite RQC; clear - Hdnc; lia
        | exact Hpos].
      - split; [clear - Hs0b Hoff; lia|]. split; [clear - Hs0b Hdnl Hoff C1; unfold TT_HI in *; lia|].
        split; [|split; [clear - Htap Hs0 Hl0 Hdnl Hdnc Hoff HUlen Rq0; unfold tt_apart in Htap; lia|]].
        + intros a Ha. split; [|rewrite Usp2; clear - Ha Hs0a Hdnl Hoff HspA; unfold ESTACK, DRAIN_FRAME; lia].
          rewrite KALLM by (clear - Ha Hs0a Hs0b Hdnl Hoff HspA C1; unfold TT_HI, DRAIN_FRAME in *; lia).
          replace a with (fst r0 + Z.of_nat (Z.to_nat (a - fst r0))) by (clear - Ha Hs0 Hoff; lia).
          rewrite ((tt_garr8_aview RG) W1 m1 _ _ _ Hr0g)
            by (rewrite tt_bzs_len, length_app; cbn [length]; clear - Ha Hs0 Hl0 Hdnl Hoff; lia).
          discriminate.
        + split; [apply (tt_amem_range_blk_x _ _ _ _ _ _ _ _ _ _ HARM Hr0in); clear - Hs0 Hl0 Hdnl Hoff Hdnr Rq0; lia|].
          split; [apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (fst r0)
            (Z.of_nat (length (snd r0)) + 1) (s0 + off) dn HARM Hr0in); clear - Hs0 Hl0 Hdnl Hoff Rq0; lia|].
          intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (fst r0)
            (Z.of_nat (length (snd r0)) + 1) (s0 + off) dn HARM Hr0in);
            [clear - Hs0 Hoff; lia | clear - Hs0 Hl0 Hdnl Hoff Rq0; lia | exact Hpos]. }
    cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3i & HP3 & Hd10b & Hcpy & Hfr3 & Hpres3).
    (* ---- after __asan_memcpy ---- *)
    jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
    match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3].
        intros a Ha. apply Hfr3; clear - Ha Hbceil Hdnc HspA HspB C1; unfold ESTACK, DRAIN_FRAME in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3].
        intros a Ha. apply Hfr3; clear - Ha Hbceil Hdnc HspA HspB C1; unfold ESTACK, DRAIN_FRAME in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 34 vv); [exact Uvv | | exact Hpres3].
        intros a Ha. apply Hfr3;
          clear - Ha Hvap Hvvb Hvva Rqv Hcpv Hdnc HUlen HspA C1; unfold tt_apart, AREC, ESTACK, DRAIN_FRAME, TT_HI in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3].
        intros a Ha. apply Hfr3; clear - Ha Hbceil Hdnc HspA HspB C1; unfold ESTACK, DRAIN_FRAME in *; lia.
      - apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 23 HA); [exact U23 | | exact Hpres3].
        intros a Ha. apply Hfr3;
          clear - Ha HAr GS1 GS2 Hbgs Hdnc HUlen HspA C1; unfold tt_apart, ASRC, ESTACK, DRAIN_FRAME in *; lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
    remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
    assert (HEIa : img_env VAL A_LIM Ea)
      by (rewrite HEa; apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
    assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m)
      by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
    clear HEa.
    assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDa by tt_num; exact Usp).
    pose proof (proj1 HJ3i) as HAR3.
    assert (SHOK3 : sh_ok SEGS (SOff 21 0) TT_SHD Ea (mrestrict (w_H W1) mem3)).
    { unfold sh_ok, TT_SHD. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply (shent_ok_of_range SEGS (w_H W1) mem3 Ea (SOff 21 0) 23 GS (4 * ASRC) HA 0 96).
        + exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem3 _ GS (4 * ASRC) HAR3 HGSZ).
        + apply U_atom; [rewrite OLDa by tt_num; exact E21 | tt_num].
        + apply (U_atom Ea 23 HA); [rewrite OLDa by tt_num; exact E23 | clear - HAr GS1 GS2; unfold ASRC in *; lia].
        + clear - HAr. lia.
        + clear - HAr. lia.
        + intros x Hx. clear - Hx HAr GS1 GS2. unfold SHADOW_OFF, ASRC in *. lia.
      - apply (shent_ok_of_range SEGS (w_H W1) mem3 Ea (SOff 21 0) 34 vv (AREC * hl_cap (hs_pending h1)) vv 0 16).
        + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem3 _ vv
            (AREC * hl_cap (hs_pending h1)) vv (AREC * hl_cap (hs_pending h1)) HAR3 Hvin);
            [clear - Hvvb; lia | clear - Rqv; lia].
        + apply U_atom; [rewrite OLDa by tt_num; exact E21 | tt_num].
        + apply (U_atom Ea 34 vv); [rewrite OLDa by tt_num; exact E34 | clear - Hvvb; unfold TT_HI in *; lia].
        + clear - Hvvb. lia.
        + clear - Hcpv. unfold AREC. lia.
        + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by (clear - Hcpv Hvvb Rqv; unfold AREC in *; lia).
          clear - Hx Hvapp Hvva Rqv Hcpv C1. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AREC in *. lia. }
    assert (HJ3 : @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx)
      hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mem3 md3 k1).
    { apply (ajournal_gx_pack_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp
        (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mem3 md3 k1 memS2);
        [exact HSTK2 | tt_num | rewrite !Z.add_0_r; exact HJ3i | exact HAG2 | intros y Hy; clear - Hy; lia]. }
    clear HJ3i HAG2 HOUT2.
    (* ---- 0x833f8 .. 0x8347c: the shadow checks of pending / v / pending_off, the byte loop's registers ---- *)
    paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 TTspan A_dr_feed; [tt_awr_regions UspA HDS|].
    rename HFr into FR10; rename HG0 into GR10; clear HF.
    match type of HS with st_ok_pi _ _ ?EFx _ (restrict _ ?mx) => set (EF := EFx) in HS; rename mx into msF end.
    assert (OLDF : forall m, (m < 48)%nat -> ew EF m = ew E m)
      by (intros m Hm; unfold EF; rewrite ?ew_ewset_other by tt_num; apply OLDa; exact Hm).
    assert (UspF : bv_unsigned (ew EF 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDF by tt_num; exact Usp).
    assert (KALLF : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) mem3 x).
    { intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) mem3 (ms_mem msF) FR10 x Hx).
      apply ((tt_nowr_fr RG HGSB) Ea _ (dsp0 cx - DRAIN_FRAME)); [vm_compute; reflexivity | exact UspA | exact N1 | exact N2]. }
    assert (PRESF : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
      by (intros x Hp; exact (apresent_grows _ _ _ _ GR10 (Hpres3 _ (PRESM x Hp)))).
    clear FR10 GR10.
    (* the n bytes copied: [pending_off, pending_off + n) of the head pending text *)
    set (data := firstn (Z.to_nat dn) (skipn (Z.to_nat off) (snd r0))).
    assert (Hdlen : length data = Z.to_nat dn)
      by (unfold data; rewrite length_firstn, length_skipn; clear - Hdnl Hl0 Hoff Hdnr; lia).
    assert (Hdlj : (length data <= length (re_junk e1))%nat) by (rewrite Hdlen; clear - Hjl Hdnc Hdnr; lia).
    assert (CPY : forall i, (i < length data)%nat ->
      aview SEGS (w_H W1) (ms_mem msF) (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)).
    { intros i Hi. rewrite Hdlen in Hi.
      assert (Hi' : 0 <= Z.of_nat i < dn) by (clear - Hi Hdnr; lia).
      rewrite KALLF by (clear - Hi' Hbceil Hdnc HUlen Hb4096 HspA C1; unfold DRAIN_FRAME in *; lia).
      pose proof (Hcpy (Z.of_nat i) Hi') as Hc. cbv iota in Hc. rewrite Hc.
      rewrite KALLM by (clear - Hi' Hs0a Hs0b Hdnl Hoff HspA C1; unfold TT_HI, DRAIN_FRAME in *; lia).
      replace (s0 + off + Z.of_nat i) with (fst r0 + Z.of_nat (Z.to_nat off + i)) by (clear - Hs0 Hoff; lia).
      rewrite ((tt_garr8_aview RG) W1 m1 _ _ _ Hr0g)
        by (rewrite tt_bzs_len, length_app; cbn [length]; clear - Hi Hl0 Hdnl Hoff Hdnr; lia).
      f_equal. unfold data. apply (tt_nth_data RG HGSB); [clear - Hl0 Hdnl Hoff Hdnr; lia | exact Hi]. }
    assert (KEEP : forall x, 0 <= x < 2 ^ 64 ->
      ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
      ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
      ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
      ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
      aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
    { intros x Hx N0 N1 N2 N3. rewrite Hdlen in N0.
      rewrite (KALLF x Hx N1 N2).
      rewrite (Hfr3 x Hx) by (first [clear - N0 Hdnr; lia | clear - N3; lia]).
      exact (KALLM x Hx N1 N2). }
    pose proof (tt_dmem_drb_xR cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 (ms_mem msF) _
      data HB HMEM HJ3 Hcpos Hdlj KEEP PRESF CPY) as HMEMF.
    (* the frame slots the round stored *)
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF2. cbn [ms_mem restrict] in RF2.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RF0. cbn [ms_mem restrict] in RF0.
    assert (HSAr : 4096 <= SA /\ SA + 56 <= TT_HI)
      by (clear - HGSA HSAG HG4096 HGceil C1; unfold TT_HI, AENT, ATABLE in *; lia).
    assert (R64 : forall v, 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N 8)) by (intros v Hv; exact Hv).
    assert (F18 : ew EF 18 = Z_to_bv 64 GS) by (rewrite OLDF by tt_num; exact E18).
    assert (F21 : ew EF 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDF by tt_num; exact E21).
    assert (F22 : ew EF 22 = Z_to_bv 64 SA) by (rewrite OLDF by tt_num; exact E22).
    assert (F23 : ew EF 23 = Z_to_bv 64 HA) by (rewrite OLDF by tt_num; exact E23).
    assert (F24 : ew EF 24 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat j)) by (rewrite OLDF by tt_num; exact E24).
    assert (F25 : ew EF 25 = Z_to_bv 64 (SA + 32))
      by (rewrite OLDF, (EREG 25%nat 25%bv) by tt_num; exact R25).
    assert (F26 : ew EF 26 = Z_to_bv 64 (SA + 16))
      by (rewrite OLDF, (EREG 26%nat 26%bv) by tt_num; exact R26).
    assert (F27 : ew EF 27 = Z_to_bv 64 (SA + 24))
      by (rewrite OLDF, (EREG 27%nat 27%bv) by tt_num; exact R27).
    assert (F35 : ew EF 35 = Z_to_bv 64 off) by (rewrite OLDF by tt_num; exact E35).
    assert (F36 : ew EF 36 = Z_to_bv 64 s0) by (rewrite OLDF by tt_num; exact E36).
    assert (F38 : ew EF 38 = Z_to_bv 64 dn) by (rewrite OLDF by tt_num; exact E38).
    assert (HAb : 0 <= HA /\ HA + 96 < 2 ^ 47) by (clear - HAr GS1 GS2; unfold ASRC in *; lia).
    assert (Heif : drain_b_c.ds_eintr sg = false)
      by (unfold ei in Hei0; rewrite Hei0 in Lei; destruct (drain_b_c.ds_eintr sg); [discriminate | reflexivity]).
    assert (Hpne : drain_b_c.ds_pend sg <> []) by (rewrite Hpend0; discriminate).
    assert (Hstr : dstrict sg).
    { intros r rs Hrs. rewrite Hpend0 in Hrs. injection Hrs as <- _. rewrite tt_bzs_len, <- Loff.
      clear - HoffL. lia. }
    pmkst HS.
    prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3. prreg HS (4%bv : bv 5) Y4.
    prreg HS (8%bv : bv 5) Y8. prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18.
    prreg HS (19%bv : bv 5) Y19. prreg HS (21%bv : bv 5) Y21. prreg HS (23%bv : bv 5) Y23.
    prreg HS (25%bv : bv 5) Y25.
    tt_reg HS (20%bv : bv 5) Y20. tt_reg HS (22%bv : bv 5) Y22. tt_reg HS (24%bv : bv 5) Y24.
    tt_reg HS (26%bv : bv 5) Y26. tt_reg HS (27%bv : bv 5) Y27.
    rewrite ?OLDF in Y2, Y3, Y4, Y8, Y9, Y18, Y19, Y21, Y23, Y25 by tt_num.
    match goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
    apply (Krb W1). unfold DRB_xR.
    exists (ms_regs msF), ly1, S1, hp1, (ms_mem msF), mdF, k1, (tt_junk e1 (data ++ skipn (length data) (re_junk e1))),
      h1, out1, ev1, LB1, spent, jb, aa, (drain_b_c.da_ev aa), (drain_b_c.da_erecs aa), tl, (s0 + off), r0, rs0.
    split; [unfold cfg_at; reflexivity|].
    split; [unfold spZ; rewrite Y2, (EREG 2%nat 2%bv) by tt_num; exact Hsp|].
    split; [rewrite Y3, (EREG 3%nat 3%bv) by tt_num; exact R3|].
    split; [rewrite Y4, (EREG 4%nat 4%bv) by tt_num; exact R4|].
    split; [rewrite Y18, E18; reflexivity|].
    split; [rewrite Y9, (EREG 9%nat 9%bv) by tt_num; exact R9|].
    split; [rewrite Y8, (EREG 8%nat 8%bv) by tt_num; exact R8|].
    split; [rewrite Y21, E21; reflexivity|].
    split; [rewrite Y23, E23; reflexivity|].
    split; [rewrite Y19, E38; reflexivity|].
    split; [rewrite Y25, E38; change (Z.of_nat 0) with 0; rewrite Z.sub_0_r; reflexivity|].
    split; [rewrite Y26, denot_lit_U, U_SAlu; cbn [zalu_raw];
      rewrite (U_atom EF 35 off F35), (U_atom EF 36 s0 F36) by (clear - Hoff Hs0b; unfold TT_HI in *; lia);
      rewrite zcanon_id by (unfold M64; clear - Hs0b Hdnl Hdnr Hoff; unfold TT_HI in *; lia);
      unfold w64; f_equal; change (Z.of_nat 0) with 0; ring|].
    split; [rewrite Y24, denot_lit_U, U_SAlu; cbn [zalu_raw];
      rewrite (U_atom EF 35 off F35), (U_atom EF 36 s0 F36) by (clear - Hoff Hs0b; unfold TT_HI in *; lia);
      rewrite zcanon_id by (unfold M64; clear - Hs0b Hdnl Hdnr Hoff; unfold TT_HI in *; lia);
      unfold w64; f_equal; change (Z.of_nat 0) with 0; ring|].
    split; [rewrite Y20, ((tt_den_resh RG HGSB) EF GS (Z.of_nat j) 40 F18 F24 F23 F21), ((tt_den_shA RG) EF 23 HA 40 F23 F21)
      by (clear - HAb HAr GS1 GS2 Hj4'; unfold ASRC in *; lia); reflexivity|].
    split; [rewrite Y27, ((tt_den_resh RG HGSB) EF GS (Z.of_nat j) 48 F18 F24 F23 F21), ((tt_den_shA RG) EF 23 HA 48 F23 F21)
      by (clear - HAb HAr GS1 GS2 Hj4'; unfold ASRC in *; lia); reflexivity|].
    split; [rewrite Y22, ((tt_den_resh RG HGSB) EF GS (Z.of_nat j) 56 F18 F24 F23 F21), ((tt_den_shA RG) EF 23 HA 56 F23 F21)
      by (clear - HAb HAr GS1 GS2 Hj4'; unfold ASRC in *; lia); reflexivity|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 HMEMF)))))|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 56 8%N (SOff 22 0) SA RF0 UspF);
      [repeat (first [left; reflexivity | right]) | exact (den_atom0 EF 22 SA F22 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 64 8%N (SOff 25 0) (SA + 32) RF0 UspF);
      [repeat (first [left; reflexivity | right])
      | exact (den_atom0 EF 25 (SA + 32) F25 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 48 8%N (SOff 27 0) (SA + 24) RF0 UspF);
      [repeat (first [left; reflexivity | right])
      | exact (den_atom0 EF 27 (SA + 24) F27 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 192 208 192 208 200 8%N (SOff 26 0) (SA + 16)
        RF2 UspF);
      [repeat (first [left; reflexivity | right])
      | exact (den_atom0 EF 26 (SA + 16) F26 ltac:(clear - HSAr; unfold TT_HI in *; lia))
      | apply R64; clear - HSAr; unfold TT_HI in *; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 32 8%N (SOff 23 24) (HA + 24) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_off; [exact F23 | clear - HAb; lia | clear - HAb; lia]
      | apply R64; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 24 8%N (SOff 23 56) (HA + 56) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_off; [exact F23 | clear - HAb; lia | clear - HAb; lia]
      | apply R64; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 72 8%N (SOff 23 64) (HA + 64) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply tt_den_off; [exact F23 | clear - HAb; lia | clear - HAb; lia]
      | apply R64; clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 80 8%N (tt_shA 23 16)
        (shadow_addr (HA + 16)) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply (tt_den_shA RG); [exact F23 | exact F21 | clear - HAb; lia | clear - HAb; lia]
      | apply R64, (tt_sh_range RG); clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 88 24 88 40 8%N (tt_shA 23 24)
        (shadow_addr (HA + 24)) RF0 UspF);
      [repeat (first [left; reflexivity | right]) | apply (tt_den_shA RG); [exact F23 | exact F21 | clear - HAb; lia | clear - HAb; lia]
      | apply R64, (tt_sh_range RG); clear - HAb; lia | tt_num]|].
    split; [apply (field_of_region EF _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 192 208 192 208 192 8%N (tt_shA 23 32)
        (shadow_addr (HA + 32)) RF2 UspF);
      [repeat (first [left; reflexivity | right]) | apply (tt_den_shA RG); [exact F23 | exact F21 | clear - HAb; lia | clear - HAb; lia]
      | apply R64, (tt_sh_range RG); clear - HAb; lia | tt_num]|].
    split; [exact Erecs|].
    split; [clear - Hs0 Loff; lia|].
    split; [change (dnum sg) with dn; clear - Hdnr; lia|].
    split; [change (dnum sg) with dn; clear - Hdnr; lia|].
    split.
    { cbn [tt_junk re_junk]. change (dnum sg) with dn.
      rewrite firstn_app, Hdlen, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite Hdlen; apply le_n).
      unfold data, ddata, dhead. rewrite Hpend0, <- Loff. cbv iota.
      rewrite tt_skipn_bzs, tt_firstn_bzs. reflexivity. }
    split; [exact HMEMF|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HSAME|].
    split; [exact Lcap|]. split; [exact Lu|]. split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|].
    split; [exact Hei0|]. split; [exact Lpend|]. split; [exact Loff|]. split; [exact Lst|].
    split; [change (Z.of_nat (length (lines (drain_b_c.ds_ref sg) (firstn 0 (ddata sg))))) with 0;
      rewrite Z.add_0_r; exact Len|].
    split; [exact Lecap|].
    split; [change (firstn 0 (ddata sg)) with (@nil Z); rewrite app_nil_r; exact HHIST|].
    split.
    { unfold RSTART. split; [exact (proj1 (proj2 HHIST))|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Lwf|]. split; [exact Hstr|]. split; [exact Heif | exact Hpne]. }
    split; [exact ((tt_dpfut0 RG HGSB) cx sg jb aa tl Hlater Heif Hpne Hstr Hroom) | exact Hbud].
- (* g_s[j].eintr == 1: the EINTR round *)
  rewrite branch_eq_U, (U_atom E 32 ei E32), (U_lit E 0) in Hc by (unfold ei in *; lia).
  apply Z.eqb_neq in Hc. assert (Hei1 : ei = 1) by (clear - Hc Hei01; unfold ei in *; lia).
  (* the slot's region gets its write window over g_s[j].eintr *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG0.
  assert (RG1 : region_ok SEGS E (ms_mem (restrict (w_H W1) msB)) (set_window tt_g0 12 16)).
  { apply region_ok_rewindow; [exact RG0|]. cbn [YP09.r_base tt_g0 base_val ms_mem restrict]. rewrite U23.
    intros o Ho. apply (writable_kept (w_H W1) m1 (ms_mem msB)).
    - exact (PRES2 _).
    - exact (HAWS o ltac:(unfold ASRC; lia)). }
  pose proof (ast_ok_pi_set_region E _ _ 1 tt_g0 (set_window tt_g0 12 16) HS eq_refl eq_refl eq_refl RG1) as HS'.
  clear HS RG0 RG1. rename HS' into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond list_upd] in HS.
  (* ---- 0x83330 .. 0x8333c: the store eintr = 0, the jal to __errno_location ---- *)
  paj_run_tok_xR RUNR HS HJ SHOK TTspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
    unfold G_DR, G_SL, inG; cbn [In]. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha HAr. unfold ASRC in *. lia. }
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  match type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into msC end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  (* __errno_location: writes nothing, returns tp - 164 *)
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs msC) (ms_mem msC) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ).
    - unfold spZ at 1. rewrite Q2, Usp. lia.
    - unfold DRAIN_FRAME. reflexivity.
    - unfold DRAIN_FRAME. lia.
    - lia.
    - rewrite HDS. unfold ESTACK, DRAIN_FRAME. lia.
    - rewrite Q3, (EREG 3%nat 3%bv), R3 by (first [lia | reflexivity]). exact Hgp0.
    - rewrite Q4, (EREG 4%nat 4%bv), R4 by (first [lia | reflexivity]). exact Htp0.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros _. right. intros [].
    - intros a [].
    - intros a [].
    - intros HPRE _. exact (AERRNO ly1 S1 hp1 W1 (ms_regs msC) (ms_mem msC) _ HPRE). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat; 1%nat] HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres2].
      intros a Ha. apply Hfr2; [lia | intros [] | unfold ESTACK, DRAIN_FRAME in *; lia].
    - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 23 HA); [exact U23 | | exact Hpres2].
      intros a Ha. apply Hfr2; [unfold ASRC in *; lia | intros [] | unfold ESTACK, DRAIN_FRAME, ASRC in *; lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  clear HEa.
  prreg HS (10%bv : bv 5) R10a.
  assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
  { assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
    { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
        repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
    pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as PI0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as PI3.
    lia. }
  assert (F52 : ew Ea 52 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10a, Herr, HERRNO; reflexivity).
  assert (B52 : bv_unsigned (ew Ea 52) = as_errno B) by (rewrite F52; apply unsigned_lit_small; lia).
  apply (st_ok_pi_add_fact _ _ _ 52%nat (mkAF 0x10000 0x5fb000 0)) in HS;
    [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B52, Z.pow_0_r, Z.mod_1_r; lia ].
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VERR & AWERR & _).
  apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 52%nat) 0 4 0 4 [])) in HS;
    [ | vm_compute; reflexivity
      | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite B52; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
        [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR3); apply (apresent_grows _ _ _ _ GR2);
          apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (AWERR o Ho) ]
      | lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
        apply all_disjoint_of_extents; unfold extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B52, (OLDa 2%nat), (OLDa 23%nat), Usp, U23 by lia;
        cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
        split; [clear - HERRI HspA C1; unfold DRAIN_FRAME in *; lia|];
        split; [pose proof (tt_errno_gs B RG HRGD) as TEG; clear - TEG HAr; unfold ASRC in *; lia | exact I] ].
  assert (UBa : U Ea (SOff 21 0) = SHADOW_OFF)
    by (apply U_atom; [rewrite (OLDa 21%nat) by lia; exact E21 | unfold SHADOW_OFF; lia]).
  assert (SHOK3 : sh_ok SEGS (SOff 21 0) [mkSHE 52 0 4] Ea (mrestrict (w_H W1) mem2)).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea (SOff 21 0) 52%nat (as_errno B) 4 (as_errno B) 0 4).
    - apply (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem2 md2 (as_errno B) 4);
        [exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) | exact HERRZ].
    - exact UBa.
    - apply U_atom; [exact F52 | lia].
    - lia.
    - lia.
    - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF. lia. }
  (* ---- 0x83340 .. 0x83360: the shadow check of errno folds, errno = EINTR, s7 / s8 reloaded, back to the head ---- *)
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK3 TTspan A_dr_top.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B52 in Ha.
      unfold G_DR, G_SL, inG; cbn [In].
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]. }
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite (OLDa 23%nat), U23 in Ha by lia.
    unfold G_DR, G_SL, inG; cbn [In]. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha HAr. unfold ASRC in *. lia. }
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  (* what the round kept: every view but g_s[j].eintr, errno and the callee's scratch *)
  assert (KEEPE : forall x, 0 <= x < 2 ^ 64 -> ~ (HA + 12 <= x < HA + 16) -> ~ (as_errno B <= x < as_errno B + 4) ->
    ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
  { intros x Hx N1 N2 N3.
    rewrite (aview_kept_out _ _ (w_H W1) mem2 (ms_mem msF) FR4 x Hx).
    2:{ intros (r & Hin & Hr). vm_compute in Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite ?(OLDa 23%nat), ?U23, ?B52 in Hr by lia; lia. }
    rewrite (Hfr2 x Hx (fun f => f) ltac:(clear - N3; lia)).
    rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msB) (ms_mem msC) FR3 x Hx).
    2:{ intros (r & Hin & Hr). vm_compute in Hin.
        destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?U23 in Hr; lia. }
    exact (KALL2 x). }
  assert (PRESE : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
    by (intros x Hp; exact (apresent_grows _ _ _ _ GR4 (Hpres2 _ (apresent_grows _ _ _ _ GR3 (PRES2 x Hp))))).
  match type of HS with st_ok_pi _ _ ?EFx _ _ => set (EF := EFx) in HS end.
  assert (OLDF : forall m, (m < 48)%nat -> ew EF m = ew E m)
    by (intros m Hm; unfold EF; rewrite ?ew_ewset_other by lia; apply OLDa; exact Hm).
  assert (U23F : bv_unsigned (ew EF 23) = HA) by (rewrite OLDF by lia; exact U23).
  assert (B52F : bv_unsigned (ew EF 52) = as_errno B) by (unfold EF; rewrite ?ew_ewset_other by lia; exact B52).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RGE. cbn [ms_mem restrict] in RGE.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RGG. cbn [ms_mem restrict] in RGG.
  assert (VERRF : val_mem SEGS (arm W1 (ms_mem msF)) (as_errno B) 4 4).
  { pose proof (field_of_region EF _ 52%nat (as_errno B) _ 0 4 0 4 0 4%N (SLit 4) 4 RGE B52F) as VF.
    rewrite Z.add_0_r in VF. apply VF; [left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
  assert (V12F : val_mem SEGS (arm W1 (ms_mem msF)) (HA + 12) 4 0).
  { apply (field_of_region EF _ 23%nat HA _ 12 40 12 16 12 4%N (SLit 0) 0 RGG U23F);
      [left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3. prreg HS (4%bv : bv 5) Y4.
  prreg HS (8%bv : bv 5) Y8. prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18.
  prreg HS (21%bv : bv 5) Y21. prreg HS (22%bv : bv 5) Y22. prreg HS (25%bv : bv 5) Y25.
  prreg HS (26%bv : bv 5) Y26. prreg HS (27%bv : bv 5) Y27.
  tt_reg HS (23%bv : bv 5) Y23. tt_reg HS (24%bv : bv 5) Y24.
  rewrite ?OLDF, ?OLDa in Y2, Y3, Y4, Y8, Y9, Y18, Y21, Y22, Y25, Y26, Y27 by lia.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr. apply EREG; assumption. }
  pose proof (tt_dmem_eintr_xR cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 (ms_mem msF) _
    HB HMEM HJ2 KEEPE PRESE V12F VERRF) as HMEMF.
  pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
  assert (HEIT : drain_b_c.ds_eintr sg = true)
    by (unfold ei in Hei1; rewrite Hei1 in Lei; destruct (drain_b_c.ds_eintr sg); [reflexivity | discriminate]).
  match goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  apply (Kdi HEIT W1). unfold DI_xR.
  exists (ms_regs msF), ly1, S1, hp1, (ms_mem msF), mdF, k1, e1, (tt_clr_ei h1), out1, 4, LB1, spent, jb, aa, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite (RK _ 2%nat Y2) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite (RK _ 3%nat Y3) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite (RK _ 4%nat Y4) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite (RK _ 22%nat Y22) by (first [lia | reflexivity]); exact R22|].
    split; [rewrite (RK _ 25%nat Y25) by (first [lia | reflexivity]); exact R25|].
    split; [rewrite (RK _ 27%nat Y27) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite (RK _ 26%nat Y26) by (first [lia | reflexivity]); exact R26|].
    split; [rewrite (RK _ 18%nat Y18) by (first [lia | reflexivity]); exact R18|].
    split; [rewrite (RK _ 9%nat Y9) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite (RK _ 8%nat Y8) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite (RK _ 21%nat Y21) by (first [lia | reflexivity]); exact R21|].
    split.
    - rewrite Y23. apply ((tt_den_shA RG) EF 22 SA 32); [rewrite OLDF by lia; exact E22 | rewrite OLDF by lia; exact E21
      | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia
      | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia].
    - rewrite Y24. rewrite ((tt_den_shA RG) EF 22 SA 0); [rewrite Z.add_0_r; reflexivity | rewrite OLDF by lia; exact E22
      | rewrite OLDF by lia; exact E21 | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia
      | clear - HGSA HSAG HG4096 HGceil C1; unfold AENT, ATABLE in *; lia]. }
  split; [exact HMEMF|].
  split; [exact HnoNUL|]. split; [exact Hused|].
  split.
  { unfold DLINK. cbn [tt_clr_ei hs_eintr]. unfold dclr. cbn [drain_b_c.ds_eintr].
    split; [exact Lcap|]. split; [exact Lu|]. split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|].
    split; [reflexivity|]. split; [exact Lpend|]. split; [exact Loff|]. split; [exact Lst|].
    split; [exact Len|]. split; [exact Lecap | exact Lwf]. }
  split; [exact HSAME|]. split; [exact HHIST|]. split; [exact HJ1|].
  split; [exact ((tt_dlater_eintr RG) cx sg jb aa tl Hlater HEIT Hroom) | exact Hbud].
Qed.

End wR.

(* ---- the strict pieces: each is its R twin at R := @wle SEGS ---- *)
(* the memory core of a cut carried across a stretch that stores nothing (a Theorem Labs lane's dt_DMEM_kept) *)
Lemma tt_DMEM_kept_x : forall cx hp ly1 S1 hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
eapply (tt_DMEM_kept_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma tt_dmem_eintr_x : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF,
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) -> ~ (as_errno B <= x < as_errno B + 4) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
val_mem SEGS (arm W1 mF) (dHA RG cx + 12) 4 0 ->
val_mem SEGS (arm W1 mF) (as_errno B) 4 4 ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 mF mdF k1 e1 (tt_clr_ei h1) (dclr sg) out1 4 sent LB1.
Proof.
eapply (tt_dmem_eintr_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma tt_dmem_drb_x : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF
  (data : list byte),
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
0 < re_cap e1 -> (length data <= length (re_junk e1))%nat ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
   ~ (dsp0 cx - DRAIN_FRAME + 24 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
   ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 208) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
(forall i, (i < length data)%nat ->
   aview SEGS (w_H W1) mF (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)) ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 mF mdF k1 (tt_junk e1 (data ++ skipn (length data) (re_junk e1))) h1 sg out1
  ev1 sent LB1.
Proof.
eapply (tt_dmem_drb_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Theorem dr_toptail_x : dr_toptail_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_toptail_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

End cx.
End bx.
End ax.
