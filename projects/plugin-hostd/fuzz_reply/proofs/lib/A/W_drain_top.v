(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the TOP segment of the ASan walk of fuzz_reply's drain
   (DI 0x831f8 -> grow/realloc, source_of scan, EINTR round, empty-pending -> DEND, data round with __asan_memcpy
   -> DRB 0; then reference_feed's byte loop dr_feed / dr_feeds).  Statements fixed in W_drain_cx.v
   (dr_top_stmt / dr_feed_stmt / dr_feeds_stmt).  The call-site technique follows the finished w2 walk
   lib/A/W_lp_tail.v (allocator + __asan_memcpy over ajournal_gx) and W_send_line_loop.v / W_send_line_entry.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_top.v, with its module paths changed; 6076 of its 6173 lines of code are new or changed and 12 lines of the source are left out. *)
(* The TOP segment of the ASan walk of fuzz_reply's drain
   (DI 0x831f8 -> grow/realloc, source_of scan, EINTR round, empty-pending -> DEND, data round with __asan_memcpy
   -> DRB 0).  Statement fixed in W_drain_cx.v (dr_top_stmt); reference_feed's byte loop (dr_feed_stmt /
   dr_feeds_stmt) is W_drain_feed.v's dr_feed_p / dr_feeds_p.  The call-site technique follows the finished w2 walk
   lib/A/W_lp_tail.v (allocator + __asan_memcpy over ajournal_gx) and W_send_line_loop.v / W_send_line_entry.v. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx W_drain_cx
W_drain_topb_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_drain_tr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

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
(* a ROM byte survives a callee's journal (W_journal.v rom_out / ajournal_gx_rom_view): it is not a walk global,
   errno or the sink's overflow head, and if it is an allocator static it is pinned as an AR const cell
   (rom_pinned; W1 45a3cc9bdd0).  The instance discharges it at the pinned placement by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
(* aout_at's three read-only cells are program globals off the allocator's statics, so an allocator or program
   call keeps them (found by GsFree at free #2: they are not in G_DR; send_line's W_send_line_cx.v HGO) *)
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
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
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
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- shared helpers for the TOP walk (prefixed dt_ to avoid integration clashes) ---- *)
Definition DBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* shadow address of (atom_m + c): ((atom_m + c) >> 3) + SHADOW_OFF, with atom 21 = SHADOW_OFF (as in W_drain_drop.v dr_shA). *)
Definition dt_shA (m : nat) (c : Z) : cval :=
  CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0)).
(* (g_s + c) >> 3 : a precomputed shifted g_s field address (no SHADOW_OFF added yet); g_s = atom 18. *)
Definition dt_gsh (c : Z) : cval := CVal 8 (SAlu ALU_SRL (SOff 18 c) (SLit 3)).
(* membership in the walk's globals G_DR *)
Ltac dt_ing_tac := unfold G_DR; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].

(* ---- Byte algebra of the relay entry's fields (the form of this lane's W_gsbytes_scratch.v). ----
   RelayRep.v:21 entry_bytes e = le4 fd ++ le4 eof ++ le4 skip ++ pad1 ++ le8 buf ++ le8 used ++ le8 cap
   ++ le8 hp ++ le4 nheld ++ pad2, so s->buf is at + 16, s->used at + 24 and s->cap at + 32. *)
Lemma dt_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma dt_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma dt_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof.
intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. reflexivity.
Qed.
Lemma dt_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma dt_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0)))
  by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, dt_nth_zle by exact Hk. rewrite dt_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma dt_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.
Lemma dt_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H KL. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (KL x Hx).
Qed.
Lemma dt_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat)
  by (rewrite dt_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite dt_nth_le_bytes by assumption. reflexivity.
Qed.
Lemma dt_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Lemma dt_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac dt_len := rewrite ?length_app, ?dt_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes;
  cbn [length].

Lemma dt_entry_buf : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_buf e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 16) 8 (re_buf e).
Proof.
intros W m SA e Hp1 Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 5 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dt_le8_bytes (re_buf e) Hv) in H.
apply (dt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (dt_garr8_at _ _ _ _ H). dt_len. lia.
Qed.
Lemma dt_entry_used : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_used e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 24) 8 (re_used e).
Proof.
intros W m SA e Hp1 Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 4 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dt_le8_bytes (re_used e) Hv) in H.
apply (dt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (dt_garr8_at _ _ _ _ H). dt_len. lia.
Qed.
Lemma dt_entry_cap : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_cap e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 32) 8 (re_cap e).
Proof.
intros W m SA e Hp1 Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 3 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dt_le8_bytes (re_cap e) Hv) in H.
apply (dt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (dt_garr8_at _ _ _ _ H). dt_len. lia.
Qed.
Lemma dt_entry_fd : forall (W : world SEGS) m SA e,
0 <= re_fd e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) SA 4 (re_fd e).
Proof.
intros W m SA e Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 8 (apply garr8_app in H as [H _]). apply garr8_app in H as [H _].
rewrite (dt_le4_bytes (re_fd e) Hv) in H.
apply (dt_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hv | exact H].
Qed.

(* ---- The walk's symbolic values: a shadow address and a pre-shifted g_s field address. ---- *)
#[local] Notation dt_sh m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0)).
#[local] Notation dt_gv c := (SAlu ALU_SRL (SOff 18 c) (SLit 3)).
#[local] Notation BxT := (SOff 21 0).
(* a register read off a symbolic state, with its value left as the state's own expression *)
Ltac dt_reg HS r Hr :=
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
(* no byte is in a region's write window: every region of a read-only stretch has whi <= wlo *)
Lemma dt_nowr_lem : forall E (rs : smem),
forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true -> forall x, ~ in_wrange E rs x.
Proof.
intros E rs HF x (r & Hin & Hr).
rewrite forallb_forall in HF. pose proof (HF r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.
Lemma dt_den_reg : forall E (n : nat) (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma dt_U_gv : forall E v c, ew E 18 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (dt_gv c) = (v + c) / 8.
Proof.
intros E v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 18 v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma dt_U_sh : forall E m v c, ew E m = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (dt_sh m c) = shadow_addr (v + c).
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
Lemma dt_den_sh : forall E m v c, ew E m = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> sv_denot E (dt_sh m c) = w64 (shadow_addr (v + c)).
Proof.
intros E m v c Hn H21 Hv Hc. rewrite denot_lit_U. unfold w64. f_equal.
exact (dt_U_sh E m v c Hn H21 Hv Hc).
Qed.
Lemma dt_den_gv : forall E v c, ew E 18 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (dt_gv c) = w64 ((v + c) / 8).
Proof.
intros E v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. exact (dt_U_gv E v c Hn Hv Hc).
Qed.

(* ---- The growth test (0x83220): (cap - used) >> 12 is nonzero exactly when the round needs no growth. ---- *)
Lemma dt_U_room : forall E cap used,
bv_unsigned (ew E 33) = cap -> bv_unsigned (ew E 34) = used -> 0 <= used <= cap -> cap <= 16384 ->
U E (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))) = cap - used.
Proof.
intros E cap used H33 H34 Hu Hc.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite !U_SOff, U_SLit, H33, H34, !Z.add_0_r.
rewrite (zcanon_id used), (zcanon_id cap) by (unfold M64; lia).
change (zcanon (-1)) with (M64 - 1).
replace (zcanon (used * (M64 - 1))) with (zcanon (- used)).
2:{ unfold zcanon. replace (used * (M64 - 1)) with (- used + used * M64) by lia.
    symmetry. apply Z_mod_plus_full. }
unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace (cap + - used) with (cap - used) by lia.
apply Z.mod_small. lia.
Qed.
Lemma dt_bnez_room : forall E cap used,
bv_unsigned (ew E 33) = cap -> bv_unsigned (ew E 34) = used -> 0 <= used <= cap -> cap <= 16384 ->
branch_taken BC_NE
  (sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))) (SLit 12)))
  (sv_denot E (SLit 0)) = (4096 <=? cap - used).
Proof.
intros E cap used H33 H34 Hu Hc. rewrite branch_ne_U.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (dt_U_room E cap used H33 H34 Hu Hc), U_SLit, (zcanon_id 12) by (unfold M64; lia).
change (Z.land 12 63) with 12. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
rewrite (zcanon_id ((cap - used) / 4096))
  by (unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite U_lit by lia.
destruct (Z.leb_spec 4096 (cap - used)) as [Hd|Hd].
- replace ((cap - used) / 4096 =? 0) with false; [reflexivity|].
  symmetry. apply Z.eqb_neq. assert (0 < (cap - used) / 4096) by (apply Z.div_str_pos; lia). lia.
- replace ((cap - used) / 4096 =? 0) with true; [reflexivity|].
  symmetry. apply Z.eqb_eq. apply Z.div_small. lia.
Qed.

(* ---- A zero-shadow range inside a live block, as the walk's shadow-entry obligation. ---- *)
Lemma dt_shent_sub : forall ly S (W : world SEGS) mem md E (m : nat) p n q lo hi,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E m p n q lo hi HAR Hin HB Hm H1 H2 H3.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
rewrite <- (aview_rd_of SEGS).
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
  eapply block_shadow_range; [exact Hbs | lia | lia].
- destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
  intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* ---- Carrying the memory core of a cut across a stretch that stores nothing. ----
   Every cut of the walk carries DMEM; a stretch with no store leaves every ASan view equal and only grows
   presence, so each of DMEM's fourteen conjuncts moves by the frame lemmas of W_rep.v.  The journal comes
   from the run itself (it is the run lemma's own conclusion), so it is a premise here. *)
Lemma dt_aentry_blks_in : forall ly S (W : world SEGS) m e,
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

Lemma dt_alist_blks_in : forall ly S (W : world SEGS) m LA l lines,
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

Lemma dt_asrc_blks_in : forall ly S (W : world SEGS) m HA h,
asrc_at B ly S W m HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W m HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
  Hexp & Hheld & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dt_alist_blks_in ly S W m (HA + 16) (hs_pending h) false Hpend b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dt_alist_blks_in ly S W m (HA + 64) (hs_expected h) true Hexp b Hb)
  |exact (dt_alist_blks_in ly S W m (HA + 80) (hs_held h) true Hheld b Hb)].
Qed.

Lemma dt_aout_blks_in : forall ly S (W : world SEGS) m c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W m c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.

Lemma dt_aentry_okx_kept : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e,
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

Lemma dt_DMEM_kept : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
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
split; [exact (dt_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => KL x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact (dt_aentry_okx_kept ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  (dt_aentry_blks_in ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  (dt_asrc_blks_in ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact (dt_aout_blks_in ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.

(* ---- The two inner cut points of the TOP segment. ----
   The segment splits at the two places where its arms meet:
     DT1 (0x8326c)  the round's growth is done: the state is dgrow s1, the relay entry's buf / cap hold
                    the grown values and the buffer has at least 4096 free bytes.  Both the no-growth arm
                    (0x83220 taken) and the realloc arm (0x83248) end here, with DI's registers.
     DT2 (0x83314)  source_of's scan found the harness slot j: s7 = &g_s[j], s8 = the shadow base + 12 j,
                    a0 = s->buf + s->used (the memcpy's destination) and a3 = s->cap - s->used (the room).
   Everything else of the two is DI's memory core, carried unchanged. *)
Definition A_dr_mid : Z := AF_fr_drain + 0x190.    (* 0x8326c, after the round's growth *)
(* A_dr_slot, the cut DT2 and the tail's statement dr_toptail_stmt are the hand-off's own file,
   lib/A/W_drain_topb_cx.v (W7Drain-2's copy; a second prover proves dr_toptail_stmt). *)

Definition DT1 (cx : dcx) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_mid) regs1 m1 md1 /\
dregs_top RG cx regs1 /\ getr regs1 19 = w64 384 /\
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud MT MMAX cx S1 spent tl.

(* ---- The four stages. ----
   NOGROW  0x831f8 .. 0x8326c with 4096 <= cap - used (the growth test at 0x83220 taken): no call.
   GROW    0x831f8 .. 0x8326c with cap - used < 4096: the new capacity, realloc #1 (0x83248, AREALLOC)
           and the stores of s->buf and s->cap.
   SCAN    0x8326c .. 0x83314: source_of's loop over the four slots of g_s (0x83294 .. 0x832e8).
   TAIL    0x83314 .. the three exits: the EINTR round (errno = EINTR through AERRNO, back to DI),
           the empty-pending test (-> DEND) and the data round's n and __asan_memcpy (-> DRB 0). *)
(* ---- The symbolic state at DI (0x831f8) for the growth test. ----
   Atoms: 18 = g_s and 21 = SHADOW_OFF are the walk's own registers (s2, s5); the extras are
   32 = the relay entry's address SA, 33 = s->cap, 34 = s->used.  The two shadow loads of the test
   (shadow(&s->cap) in s7, shadow(&s->used) at 224(sp)) are resolved by the entry's zero-shadow range. *)
Definition dt_HEAPF : afact := mkAF 4096 140737479966720 0.
Definition dt_IMGF : afact := mkAF 0x10000 0x5fb000 3.
Definition dt_regs_top : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
  22%bv (SOff 32 0)) 25%bv (SOff 32 32)) 26%bv (SOff 32 16)) 27%bv (SOff 32 24))
  23%bv (dt_sh 32 32)) 24%bv (dt_sh 32 0)) 9%bv (dt_gv 0)) 8%bv (dt_gv 4).
Definition dt_ng_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 336 0 0
  [ YP09.mkChunk 224 (dt_shA 32 24) ].
Definition dt_ng_sa : YP09.region := YP09.mkRegion (Some 32%nat) 0 56 0 0
  [ YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)) ].
Definition dt_ng_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0); (18%nat, dt_IMGF);
    (32%nat, dt_HEAPF); (33%nat, mkAF 0 16384 0); (34%nat, mkAF 0 16384 0) ] [] [].
Definition ss_ng : sstate := mkSS A_dr_top dt_regs_top [ dt_ng_frame; dt_ng_sa ] None dt_ng_facts.
Definition SHng : list shent := [ mkSHE 32 0 56 ].
Definition dt_ng_extra (SA cap used : Z) : list word := map (Z_to_bv 64) [SA; cap; used].

Lemma dt_nogrow : forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
(forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx s1 D W1 c1 HB HDI Hge K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDI as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16848) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof HEOK as (Heof & Hskipv & Hpad1 & Hpad2 & Hfdv & Hcapv & HUlen & Hucap & Hbufc & Hnheld & Hheldc &
  HND1 & HND2 & Hkeys).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= 16384) by lia.
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_ng_extra (dxSA cx) (re_cap e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs1 25 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs1 26 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs1 23 = sv_denot E (dt_sh 32 32))
  by (rewrite (dt_den_sh E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs1 24 = sv_denot E (dt_sh 32 0))
  by (rewrite (dt_den_sh E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite (dt_den_gv E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs1 8 = sv_denot E (dt_gv 4))
  by (rewrite (dt_den_gv E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_ng
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ng. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_ng_frame, dt_ng_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
        [ exact (dt_den_sh E 32 (dxSA cx) 24 E32 E21 ltac:(lia) ltac:(lia))
        | unfold shadow_addr, SHADOW_OFF;
          (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                  | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia); zside])
        | zside
        | exact F224 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [ exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [ exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_cap W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_ng_frame, dt_ng_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_ng_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF.
    cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUN BR HS SHOK DBspan.
- (* 4096 <= cap - used: the round needs no growth, straight on to 0x8326c *)
  paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_mid.
  { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  rewrite wvb_collapse in HJ.
  (* the two runs store nothing: every region of ss_ng is read-only, so no byte of the walk's memory moves *)
  assert (Hnw : forall x, ~ in_wrange E (ss_mem ss_ng) x).
  { intros x (r & Hin & Hr). cbv [ss_mem ss_ng dt_ng_frame dt_ng_sa] in Hin.
    destruct Hin as [Hq|[Hq|[]]]; subst r;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a.
    rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (Hnw _))).
    exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (Hnw _))). }
  assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ _ HG1 (apresent_grows _ _ _ _ HG0 Ha))).
  dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
  dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (18%bv : bv 5) X18.
  dt_reg HS (21%bv : bv 5) X21. dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23.
  dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26.
  dt_reg HS (27%bv : bv 5) X27.
  pmkst HS.
  apply K. rewrite (dgrow_id s1 Hge). unfold DT1.
  eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
    split; [rewrite X25; exact (eq_trans (eq_sym R25') R25)|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
    split; [rewrite X26; exact (eq_trans (eq_sym R26') R26)|].
    split; [rewrite X18, (dt_den_reg E 18 _ E18); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
    split; [rewrite X8; exact (eq_trans (eq_sym R8') R8)|].
    split; [rewrite X21, (dt_den_reg E 21 _ E21); reflexivity|].
    split; [rewrite X23; exact (eq_trans (eq_sym R23') R23)
           |rewrite X24; exact (eq_trans (eq_sym R24') R24)]. }
  split; [dt_reg HS (19%bv : bv 5) X19; rewrite X19; cbn [sv_denot]; reflexivity|].
  split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms0) md1 _ k1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
  split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hge|].
  split; [exact Hlater | exact Hbud].
- rewrite (dt_bnez_room E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_gt in Hc.
  pose proof HLINK as (Lcap & Lu & Lrest).
  assert (Hulen : ulen s1 = re_used e1)
    by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUlen).
  rewrite <- Lcap, Hulen in Hge. lia.
Qed.

(* ---- What the realloc site needs of the walk's journal and of the buffer it hands over. ---- *)
(* The allocator rules are stated over the donor journal; drain's walk carries ajournal_gx at XO = 0, which
   differs only by the overlaid start memory the rules leave alone (W_drain_gs.v gs_gx_open / gs_gx_close). *)
Lemma dt_gx_open : forall G STK sp0 FP ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k,
@ajournal_gx _ SK SEGS B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal SEGS B STK sp0 FP ly S W0 memS md own lyc Sc W memc mdc k.
Proof.
intros G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi. exists memS. split; [exact HSTK|]. split; [exact Hag | exact HJi].
Qed.
Lemma dt_gx_close : forall G STK sp0 FP ly S W0 mem md own ly2 S2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal SEGS B STK sp0 FP ly S W0 memS md own ly2 S2 W2 mem2 md2 k2 ->
@ajournal_gx _ SK SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2 memS HSTK Hag HJ.
apply (ajournal_gx_pack SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2 memS);
  [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha; lia].
Qed.

(* No live block is listed twice: two copies would have to be disjoint from themselves. *)
Lemma dt_no_dup_block : forall ly S (W : world SEGS) mem md x l,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: x :: l) -> 0 <= snd x -> False.
Proof.
intros ly S W mem md x l HAR HP Hn.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x x l HAR HP) as Hd.
pose proof (req_size_pos (snd x) Hn) as (Hr & _).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* A byte of a block of the entry's own footprint list is a byte the walk declared. *)
Lemma dt_inFP_of_blocks : forall bl p n i SA,
In (p, n) bl -> 0 <= i < req_size n -> inFP ((SA, SA + AENT) :: ablocks_fp bl) (p + i).
Proof.
intros bl p n i SA Hin Hi. exists (p, p + req_size n). split; [right|cbn [fst snd]; lia].
exact (in_map (fun b => (fst b, fst b + req_size (snd b))) bl (p, n) Hin).
Qed.

(* The buffer the round hands to realloc: if it was already a block when drain was entered, it is one of the
   blocks the walk declared.  It cannot be the relay's table (its requested size is not a capacity), and it
   cannot be one of the blocks drain found live and left alone (dxrest): the entry's buffer is a block at the
   cut too, so the cut's block list would hold it twice. *)
Lemma dt_buf_fp : forall cx ly1 S1 (W1 : world SEGS) m1 md1 bl p n,
AR SEGS B ly1 S1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: bl ++ dxrest cx) -> In (p, n) bl ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++
     dxrest cx) ->
In (p, n) (ablocks B (dxly cx) (dxS cx)) -> 0 <= n -> n <> ATABLE ->
forall i, 0 <= i < req_size n -> inFP (dFP cx) (p + i).
Proof.
intros cx ly1 S1 W1 m1 md1 bl p n HAR HPc Hbl HP0 Hin0 Hn Hnt i Hi.
unfold dFP, dr_fp.
assert (Hin : In (p, n) ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
  aout_blks (dxcap cx) (dxout cx) ++ dxrest cx)) by (eapply Permutation_in; [exact HP0 | exact Hin0]).
destruct Hin as [Heq | Hin]; [injection Heq as _ Heq; congruence|].
apply in_app_or in Hin as [Hin | Hin]; [exact (dt_inFP_of_blocks _ p n i _ (in_or_app _ _ _ (or_introl Hin)) Hi)|].
apply in_app_or in Hin as [Hin | Hin];
  [exact (dt_inFP_of_blocks _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hin)))) Hi)|].
apply in_app_or in Hin as [Hin | Hrest];
  [exact (dt_inFP_of_blocks _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hin)))) Hi)|].
exfalso.
destruct (in_split _ _ Hbl) as (b1 & b2 & Eb).
destruct (in_split _ _ Hrest) as (d1 & d2 & Ed).
apply (dt_no_dup_block ly1 S1 W1 m1 md1 (p, n) ((dxG cx, ATABLE) :: b1 ++ b2 ++ d1 ++ d2)); [exact HAR | | exact Hn].
eapply Permutation_trans; [exact HPc|].
rewrite Eb, Ed, <- !app_assoc.
apply Permutation_sym.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: b1) (l2 := b2 ++ d1 ++ (p, n) :: d2).
cbn [app]. rewrite !app_assoc.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: (b1 ++ b2) ++ d1) (l2 := d2).
apply Permutation_refl.
Qed.

(* Twice the old capacity, as the slli at 0x83230 leaves it. *)
Lemma dt_den_sll : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v -> 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 1)) = w64 (v * 2).
Proof.
intros E n v Hn Hv Hv2. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn ltac:(lia)), U_SLit.
rewrite (zcanon_id 1) by (unfold M64; lia). change (Z.land 1 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
apply zcanon_id. unfold M64. lia.
Qed.

(* The capacity test at 0x83224. *)
Lemma dt_bnez_atom : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof.
intros E n v Hn Hv. rewrite branch_ne_U.
rewrite (U_atom E n v Hn ltac:(lia)), U_lit by lia.
destruct (Z.eqb_spec v 0) as [->|Hne]; reflexivity.
Qed.
(* ---- GROW: DI 0x831f8 with cap - used < 4096 -> realloc #1 (0x83248) -> DT1 0x8326c. ----
   The state the stretch needs: DI's registers, the frame's two shadow slots (216 = shadow(SA + 16), 224 =
   shadow(SA + 24)) and the entry's buf / used / cap.  Nothing is stored before the call, so the window is
   empty here; the two stores (s->buf at 0x8325c, s->cap at 0x83268) are on the state the call hands back. *)
Definition dt_gr_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 336 0 0
  [ YP09.mkChunk 216 (dt_shA 32 16); YP09.mkChunk 224 (dt_shA 32 24) ].
Definition dt_gr_sa : YP09.region := YP09.mkRegion (Some 32%nat) 0 56 0 0
  [ YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
    YP09.mkChunk 32 (CVal 8 (SOff 33 0)) ].
Definition dt_gr_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0); (18%nat, dt_IMGF);
    (32%nat, dt_HEAPF); (33%nat, mkAF 0 16384 0); (34%nat, mkAF 0 16384 0) ] [] [].
Definition ss_gr : sstate := mkSS A_dr_top dt_regs_top [ dt_gr_frame; dt_gr_sa ] None dt_gr_facts.
Definition dt_gr_extra (SA cap used buf : Z) : list word := map (Z_to_bv 64) [SA; cap; used; buf].
Definition A_dr_rret : Z := AF_fr_drain + 0x170.   (* 0x8324c, where realloc #1 returns *)

(* The capacity the round asks for: 8192 from nothing, twice the old one otherwise (Prog/drain_b_c.v grow_tr). *)
Lemma dt_gcap_grow : forall cap used, used <= cap -> cap - used < 4096 ->
gcap cap used = (if cap =? 0 then 8192 else cap * 2).
Proof.
intros cap used Hu Hlt. unfold gcap, drain_b_c.grow_tr.
rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt). cbn [fst snd]. reflexivity.
Qed.

(* The round's growth always leaves at least 4096 free: from nothing it takes 8192, and a buffer only grows
   when it has less than 4096 free, which for the splitter's 6000-byte partial can only be the 8192 one. *)
Lemma dt_grow_room : forall s1,
drain_b_c.ds_cap s1 - ulen s1 < 4096 -> 0 <= ulen s1 <= APARTIAL -> ulen s1 <= drain_b_c.ds_cap s1 ->
(drain_b_c.ds_cap s1 = 0 \/ drain_b_c.ds_cap s1 = 8192 \/ drain_b_c.ds_cap s1 = 16384) ->
4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1).
Proof.
intros s1 Hlt Hu Huc Hc.
change (ulen (dgrow s1)) with (ulen s1).
change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) Huc Hlt).
unfold APARTIAL in Hu. destruct Hc as [Hq|[Hq|Hq]]; rewrite Hq; cbn [Z.eqb]; lia.
Qed.

(* What the walk may still spend, as the allocator rules ask for it (W_drain_gs.v gs_mo_ok_of). *)
Lemma dt_mo_ok_of : forall cx S1 spent tl c,
mo_ok MT (dxS cx) (dcost MT cx) -> dbud MT MMAX cx S1 spent tl ->
0 <= c -> c <= tr_cost MT tl -> mo_ok MT S1 c.
Proof.
intros cx S1 spent tl c Hok (Hle & Hsp & Hcost & _ & _) Hc0 Hc.
apply (mok_station MT (dxS cx) S1 (dcost MT cx) spent c MTL Hok Hle); lia.
Qed.

(* The three meters over an append, and what the growth's own request costs. *)
Lemma dt_tr_cost_app : forall (t1 t2 : dtrace), tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof.
intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma dt_tr_alloc_app : forall (t1 t2 : dtrace), tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
intros t1 t2. unfold tr_alloc. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma dt_tr_max_nonneg : forall (t : dtrace), 0 <= tr_max t.
Proof.
intros t. unfold tr_max. induction t as [|ev t IH]; [cbn [fold_right]; lia|].
cbn [fold_right]. destruct ev; lia.
Qed.
Lemma dt_tr_max_app : forall (t1 t2 : dtrace), tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros t1 t2. pose proof (dt_tr_max_nonneg t2) as H2. unfold tr_max in *.
induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
(* The rounds still to come ask for nonnegative sizes, so what they allocate and what they cost are nonnegative.
   It needs the signs of the round state (a negative s->cap grows by a negative request): DI gives them, dgrow
   keeps them, and W_drain_tr.v's dr_di_later_meters projects them along dlater. *)
Lemma dt_later_meters : forall cx s1 D W1 c1 jb a tl,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
dlater cx (dgrow s1) jb a tl \/ dlater cx s1 jb a tl -> 0 <= tr_alloc tl /\ 0 <= tr_cost MT tl.
Proof.
intros cx s1 D W1 c1 jb a tl HB HI HL.
eapply W_drain_tr.dr_di_later_meters; eassumption.
Qed.

Lemma dt_grow_ev : forall cap used j b, 0 <= cap -> used <= cap -> cap - used < 4096 ->
tr_max (fst (drain_b_c.grow_tr cap used j b)) = gcap cap used /\
tr_alloc (fst (drain_b_c.grow_tr cap used j b)) = gcap cap used /\
tr_cost MT (fst (drain_b_c.grow_tr cap used j b)) = mo_malloc MT (gcap cap used) + mo_free MT.
Proof.
intros cap used j b Hc0 Hu Hlt.
rewrite (dt_gcap_grow cap used Hu Hlt).
unfold drain_b_c.grow_tr. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt). cbn [fst snd].
destruct (cap =? 0); cbn [tr_max tr_alloc tr_cost fold_right];
  (split; [lia|]); (split; lia).
Qed.
(* C3: the growth's one request (malloc of the new capacity from nothing, else realloc of the old capacity cap to it)
   gets its live-bytes premise from the peak of the trace it opens, and moves the live bytes by gcap - cap, so the
   peak of what follows stays in room (W_tr_peak.v tr_peak_malloc / tr_peak_realloc). *)
Lemma dt_grow_pk : forall cap used j b (t : dtrace) bb, 0 <= cap -> used <= cap -> cap - used < 4096 ->
bb + tr_peak (fst (drain_b_c.grow_tr cap used j b) ++ t) <= LIVE_MAX ->
bb + gcap cap used <= LIVE_MAX /\ bb - cap + gcap cap used + tr_peak t <= LIVE_MAX.
Proof.
intros cap used j b t bb Hc0 Hu Hlt H.
pose proof (W_tr_peak.tr_peak_nonneg t) as Ht.
rewrite (dt_gcap_grow cap used Hu Hlt).
unfold drain_b_c.grow_tr in H. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt) in H. cbn [fst app] in H.
destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota in H |- *;
  [rewrite W_tr_peak.tr_peak_malloc in H | rewrite W_tr_peak.tr_peak_realloc in H]; lia.
Qed.

(* The round's growth is the first thing the rest of the walk owes the allocator: one request for the new
   capacity, then the rounds of the grown state (W_drain_model.v drun_grow). *)
Lemma dt_grow_tr : forall cx s1 jb a tl,
dlater cx s1 jb a tl -> 4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1) ->
exists tl2,
  tl = fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf a)) ++ tl2 /\
  dlater cx (dgrow s1)
    (jb + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf a))))
    (agrow s1 jb a) tl2.
Proof.
intros cx s1 jb a tl (fuel & Hneed & Hwf & Htr & Hfin) Hroom.
destruct fuel as [|f]; [unfold dneed in Hneed; lia|].
rewrite (drun_grow f (dlive cx) (dxmx cx) s1 jb a Hroom) in Htr, Hfin. cbn [fst snd] in Htr, Hfin.
eexists. split; [exact (eq_sym Htr)|].
exists (S f). split; [unfold dneed, pstream; cbn [dgrow drain_b_c.ds_pend drain_b_c.ds_off
  drain_b_c.ds_eintr]; unfold dneed, pstream in Hneed; lia|].
split; [|split; [reflexivity | exact Hfin]].
unfold dwf in Hwf |- *. cbn [dgrow drain_b_c.ds_off drain_b_c.ds_pend]. exact Hwf.
Qed.

(* ---- The symbolic state at 0x8324c, where realloc #1 returns. ----
   The callee-saved registers as at DI (dt_regs_top over atom 32 = SA); a0 = res is atom 10 and s4 = the new
   capacity atom 20, both the post's own register values.  The frame chunk at 216 is shadow(&s->buf) for the
   shadow check before the first store; the two stores write [SA + 16, SA + 24) (s->buf) and [SA + 32, SA + 40)
   (s->cap), one region each, so that every other byte of the entry is the byte the call left. *)
Definition dt_gp_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 336 0 0
  [ YP09.mkChunk 216 (dt_shA 32 16) ].
Definition dt_gp_buf : YP09.region := YP09.mkRegion (Some 32%nat) 16 24 16 24 [].
Definition dt_gp_cap : YP09.region := YP09.mkRegion (Some 32%nat) 32 40 32 40 [].
Definition dt_gp_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0); (18%nat, dt_IMGF); (32%nat, dt_HEAPF) ] [] [].
Definition ss_gp : sstate := mkSS A_dr_rret dt_regs_top [ dt_gp_frame; dt_gp_buf; dt_gp_cap ] None dt_gp_facts.
Definition dt_gp_extra (SA : Z) : list word := map (Z_to_bv 64) [SA].

Ltac dt_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

(* the `beqz a0` at 0x8324c *)
Lemma dt_beqz_atom : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v Hn Hv. rewrite branch_eq_U.
rewrite (U_atom E n v Hn Hv), U_lit by lia. reflexivity.
Qed.

(* ---- Byte transport across the call and the two stores (the form of W_gsfree_scratch.v's gm_ lemmas). ---- *)
Lemma dt_in_zr_dec : forall x r, {in_zr x r} + {~ in_zr x r}.
Proof.
intros x r. unfold in_zr. destruct (Z_le_gt_dec (fst r) x); destruct (Z_lt_ge_dec x (fst r + snd r));
[left; lia | right; lia | right; lia | right; lia].
Qed.

Lemma dt_bk_trans : forall (W0 : world SEGS) m0 (W1 : world SEGS) m1 (W2 : world SEGS) m2 x,
abyte_kept W0 m0 W1 m1 x -> abyte_kept W1 m1 W2 m2 x -> abyte_kept W0 m0 W2 m2 x.
Proof.
intros W0 m0 W1 m1 W2 m2 x [V1 P1] [V2 P2]. split; [rewrite V2; exact V1 | intros H; exact (P2 (P1 H))].
Qed.

(* a byte stays writable across two worlds when its presence is kept *)
Lemma dt_wr_kept2 : forall (H H2 : word -> bool) (m m2 : word -> option byte) a,
(apresent H m a -> apresent H2 m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H2 m2) a.
Proof.
intros H H2 m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; destruct (H2 (Z_to_bv 64 a)) eqn:EH2; intros Hw.
- exact Hw.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
  destruct (Hp (conj EH (ex_intro _ b Em))) as [Hc _]. rewrite Hc in EH2. discriminate.
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
  + destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* a byte of a writable image segment whose view is defined is writable *)
Lemma dt_img_wr : forall (W : world SEGS) m a,
in_img SEGS a -> ~ in_rom SEGS a -> aview SEGS (w_H W) m a <> None -> writable_at SEGS (arm W m) a.
Proof.
intros W m a Hi Hr Hv.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H W (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (Hfn : find_segment SEGS a 1 <> None) by (apply find_segment_img; exact Hi).
destruct (find_segment SEGS a 1) as [sg|] eqn:Hf; [|exfalso; exact (Hfn eq_refl)].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & Hlo & Hhi).
assert (Hw : seg_writable sg = true).
{ destruct (seg_writable sg) eqn:E; [reflexivity|]. exfalso. apply Hr. exists sg.
  split; [exact Hin|]. split; [exact E|]. lia. }
revert Hv. unfold aview, writable_at, arm, mbyte, wview, mrestrict, seg_rom, memory_read.
rewrite HA. rewrite ?Ha.
destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; discriminate|].
change (Z.of_N 1) with 1. rewrite Hf. cbv beta iota zeta. rewrite Hw. cbv beta iota.
destruct (seg_readable sg); [|intros H; exfalso; apply H; reflexivity].
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at _ _); [intros _; discriminate | intros H; exfalso; apply H; reflexivity].
Qed.

(* two blocks at distinct places of a permutation of the live blocks are apart *)
Lemma dt_sep_head : forall ly S (W : world SEGS) m md x L y,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

Lemma dt_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.

(* every byte a list's predicate reads is in its struct or in one of its blocks *)
Lemma dt_list_fp : forall ly S (W : world SEGS) m LA l lines, alist_at B ly S W m LA l lines ->
forall r x, In r (alist_fp LA l) -> fst r <= x < snd r ->
(LA <= x < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= x < fst b + req_size (snd b).
Proof.
intros ly S W m LA l lines HL r x Hr Hx. pose proof HL as (_ & _ & _ & _ & Hnc & H6 & _ & _ & H9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn in Hx; lia|]. right.
apply in_app_iff in Hr as [Hr|Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<-|[]].
  destruct H6 as [(Hc & _) | (Hc0 & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  exists (hl_v l, AREC * hl_cap l).
  split; [unfold alist_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in *.
  unfold bzs in Hx. rewrite length_map, length_app, dt_concat_len in Hx. unfold req_size, AREC, hl_n in *.
  destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia|]. lia.
- apply in_map_iff in Hr as (t & <- & Ht).
  exists (fst t, Z.of_nat (length (snd t)) + 1).
  split; [unfold alist_blks; apply in_or_app; right;
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Ht|].
  unfold gfp in Hx. cbn [fst snd] in *.
  unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. unfold req_size.
  destruct (Z.of_nat (length (snd t)) + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.

(* every byte a source's predicate reads is in the struct source or in one of its blocks *)
Lemma dt_src_fp : forall ly S (W : world SEGS) m HA h, asrc_at B ly S W m HA h ->
forall r x, In r (asrc_fp HA h) -> fst r <= x < snd r ->
(HA <= x < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= x < fst b + req_size (snd b).
Proof.
intros ly S W m HA h HS r x Hr Hx.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Hx. exact Hx.
- right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in *. unfold bzs in Hx. rewrite length_map in Hx.
  assert (RQ : req_size APARTIAL = APARTIAL) by reflexivity. rewrite RQ. lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (dt_list_fp ly S W m (HA + 16) (hs_pending h) false Hpend r x Hr Hx) as [H | (b & Hb & Hbx)];
      [left; unfold ASRC; lia | right; exists b; split; [right; apply in_or_app; left; exact Hb | exact Hbx]].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (dt_list_fp ly S W m (HA + 64) (hs_expected h) true Hexp r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hbx]].
    * destruct (dt_list_fp ly S W m (HA + 80) (hs_held h) true Hheld r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbx]].
Qed.

(* every byte the output's predicate reads is a walk global, one of its three read-only cells, or g_out *)
Lemma dt_out_fp : forall cap out r x, In r (aout_fp B RG cap out) -> fst r <= x < snd r ->
inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x \/
(cap <> 0 /\ out <= x < out + cap).
Proof.
intros cap out r x Hr Hx. unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx;
try (left; unfold G_DR, G_SL, inG;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]; fail);
try (right; left; unfold inG;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]; fail).
destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
right; right. split; [apply Z.eqb_neq in Hc0; exact Hc0 | exact Hx].
Qed.

(* drain's frame slots, every one in [sp, sp + 336), across two worlds *)
Lemma dt_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in *. cbv zeta in *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
intros i Hi. specialize (HS i Hi).
replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | exact HS].
Qed.

Lemma dt_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
change (key_ptrs (k :: ks)) with (Mem.le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs ks).
rewrite length_app, Mem.length_le8, IH. cbn [length]. lia.
Qed.

Lemma dt_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.

Lemma dt_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite dt_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite dt_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite dt_le_byte1 by exact Hr. reflexivity.
Qed.

(* a byte run copied from one place to another (the realloc's copy of the old buffer) keeps its image *)
Lemma dt_garr8_shift : forall (W : world SEGS) m (W' : world SEGS) m' a a' l,
garr8 SEGS (arm W m) a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W') m' (a' + i) = aview SEGS (w_H W) m (a + i)) ->
garr8 SEGS (arm W' m') a' l.
Proof.
intros W m W' m' a a' l H K j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. specialize (Hv k Hk). rewrite <- Hv.
replace (Z.of_nat k) with 0 by lia. rewrite !Z.add_0_r. unfold arm.
pose proof (K (Z.of_nat j) ltac:(lia)) as E. unfold aview in E.
destruct (mbyte SEGS (mrestrict (w_H W') m') (a' + Z.of_nat j)) as [b'|],
  (mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat j)) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* the byte list a garr8 sees, read back through Z_to_bv 8 *)
Lemma dt_bzs_of_garr8 : forall mem a (l : list Z), garr8 SEGS mem a l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
intros mem a l H. unfold bzs.
apply (nth_ext _ _ 0 0); [rewrite !length_map; reflexivity|].
intros j Hj. rewrite !length_map in Hj.
rewrite (nth_indep (map bz (map (Z_to_bv 8) l)) 0 (bz (Z_to_bv 8 0))) by (rewrite !length_map; exact Hj).
rewrite List.map_nth, List.map_nth, dt_bz_bv8. destruct (H j Hj) as [_ Hr]. apply Z.mod_small. exact Hr.
Qed.

(* ---- The relay entry after the growth: s->buf = res, s->cap = nc, the bytes past the copy fresh. ---- *)
Definition dt_ge (e : rentry) (res nc : Z) (junk : list byte) : rentry :=
RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) res (re_used e) nc (re_hp e) (re_kh e) (re_pad2 e) (re_keys e)
   (re_U e) junk.
(* the entry's blocks other than its buffer *)
Definition dt_hkb (e : rentry) : list (Z * Z) :=
(if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e).

(* the 56 bytes at SA after the two stores: only s->buf [16, 24) and s->cap [32, 40) changed *)
Lemma dt_entry_grow : forall (W : world SEGS) m (W' : world SEGS) m' SA e res nc junk,
length (re_pad1 e) = 4%nat -> 0 <= res < 2 ^ 64 -> 0 <= nc < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W' m') (SA + 16) 8 res -> val_mem SEGS (arm W' m') (SA + 32) 8 nc ->
(forall x, SA <= x < SA + 16 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 24 <= x < SA + 32 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 40 <= x < SA + 56 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
length (re_pad2 e) = 4%nat ->
garr8 SEGS (arm W' m') SA (bzs (entry_bytes (dt_ge e res nc junk))).
Proof.
intros W m W' m' SA e res nc junk Hp1 Hres Hnc H Vb Vc K1 K2 K3 Hp2.
unfold entry_bytes, re_nheld in H |- *. unfold dt_ge.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys].
rewrite !dt_bzs_app, !app_assoc in H |- *.
apply garr8_app in H as [H HA10]. apply garr8_app in H as [H HA9]. apply garr8_app in H as [H HA8].
apply garr8_app in H as [H _]. apply garr8_app in H as [H HA6]. apply garr8_app in H as [H4 _].
rewrite (dt_le8_bytes res Hres), (dt_le8_bytes nc Hnc).
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 52)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_kept W m); [apply (dt_garr8_at _ _ _ _ HA10); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K3. revert Hx. dt_len. rewrite ?Hp2. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 48)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_kept W m); [apply (dt_garr8_at _ _ _ _ HA9); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K3. revert Hx. dt_len. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 40)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_kept W m); [apply (dt_garr8_at _ _ _ _ HA8); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K3. revert Hx. dt_len. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 32)); [|dt_len; rewrite ?Hp1; lia].
    apply dt_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hnc | exact Vc]. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 24)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_kept W m); [apply (dt_garr8_at _ _ _ _ HA6); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K2. revert Hx. dt_len. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 16)); [|dt_len; rewrite ?Hp1; lia].
    apply dt_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hres | exact Vb]. }
apply (dt_garr8_kept W m); [exact H4|].
intros x Hx. apply K1. revert Hx. dt_len. rewrite ?Hp1. intros Hx. lia.
Qed.

(* the new buffer's bytes: the copy of the old buffer's cap bytes (U ++ junk), then the block's own bytes *)
Lemma dt_newbuf : forall (W1 : world SEGS) m1 (W2 : world SEGS) m2 e res nc,
((re_cap e = 0 /\ re_buf e = 0 /\ re_used e = 0) \/
 (0 < re_cap e /\ Z.of_nat (length (re_junk e)) = re_cap e - re_used e /\
  garr8 SEGS (arm W1 m1) (re_buf e) (bzs (re_U e ++ re_junk e)))) ->
Z.of_nat (length (re_U e)) = re_used e -> 0 <= re_cap e <= nc ->
(0 < re_cap e -> forall i, 0 <= i < re_cap e ->
  aview SEGS (w_H W2) m2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e + i)) ->
(forall x, res <= x < res + nc -> apresent (w_H W2) m2 x) ->
exists junk, Z.of_nat (length junk) = nc - re_used e /\ garr8 SEGS (arm W2 m2) res (bzs (re_U e ++ junk)).
Proof.
intros W1 m1 W2 m2 e res nc Hb HU Hc Hcp Hpr.
assert (Hfresh : forall a k, res <= a -> a + Z.of_nat k <= res + nc ->
  exists l : list byte, length l = k /\ garr8 SEGS (arm W2 m2) a (bzs l)).
{ intros a k H1 H2.
  destruct (garr8_of_present SEGS (arm W2 m2) a k) as (l & Hl & Hg).
  { intros x Hx. destruct (Hpr x ltac:(lia)) as (Hh & bb & Hbb). exists bb.
    unfold arm, mrestrict. rewrite Hh, Hbb. reflexivity. }
  exists (map (Z_to_bv 8) l). split; [rewrite length_map; exact Hl|].
  rewrite (dt_bzs_of_garr8 _ _ _ Hg). exact Hg. }
destruct Hb as [(Hc0 & Hb0 & Hu0) | (Hcp0 & HJk & Hg)].
- assert (HU0 : re_U e = []) by (destruct (re_U e); [reflexivity | cbn [length] in HU; lia]).
  assert (Hk : res + Z.of_nat (Z.to_nat nc) <= res + nc) by (rewrite Z2Nat.id by lia; lia).
  destruct (Hfresh res (Z.to_nat nc) ltac:(lia) Hk) as (l & Hl & Hg).
  exists l. rewrite HU0, Hu0. cbn [app]. split; [rewrite Hl, Z2Nat.id by lia; lia | exact Hg].
- assert (Hk : res + re_cap e + Z.of_nat (Z.to_nat (nc - re_cap e)) <= res + nc)
    by (rewrite Z2Nat.id by lia; lia).
  destruct (Hfresh (res + re_cap e) (Z.to_nat (nc - re_cap e)) ltac:(lia) Hk) as (l & Hl & Hg2).
  exists (re_junk e ++ l). split; [rewrite length_app, Nat2Z.inj_add, Hl, Z2Nat.id by lia; lia|].
  rewrite app_assoc, dt_bzs_app. apply garr8_app. split.
  + apply (dt_garr8_shift W1 m1 W2 m2 (re_buf e) res); [exact Hg|].
    intros i Hi. apply (Hcp Hcp0). rewrite dt_bzs_len, length_app, Nat2Z.inj_add in Hi. lia.
  + apply (dt_garr8_at _ _ _ _ Hg2). rewrite dt_bzs_len, length_app, Nat2Z.inj_add. lia.
Qed.

(* the entry's invariant after the growth: the new buffer block in place of the old one, the rest kept *)
Lemma dt_aentry_okx_grow : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e res nc junk,
aentry_okx B ly S W m e ->
(nc = 8192 \/ nc = 16384) -> re_used e <= nc ->
In (res, nc) (ablocks B ly' S') -> Z.of_nat (length junk) = nc - re_used e ->
garr8 SEGS (arm W' m') res (bzs (re_U e ++ junk)) ->
akept W m W' m' (gfp (re_hp e) (bzs (key_ptrs (re_keys e))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e)) ->
(forall b, In b (dt_hkb e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' m' (dt_ge e res nc junk).
Proof.
intros ly S W m ly' S' W' m' e res nc junk
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) Hnc Hu Hin Hj Hg HK HB.
unfold aentry_okx, re_nheld in *. unfold dt_ge.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [destruct Hnc as [-> | ->]; right; [left | right]; reflexivity|].
split; [exact H7|].
split; [exact Hu|].
split; [right; split; [destruct Hnc as [-> | ->]; lia|]; split; [exact Hin|]; split; [exact Hj | exact Hg]|].
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin' & Hk1 & Hk2 & Hg')]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold dt_hkb; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg'].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [left; reflexivity | exact Hx]. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold dt_hkb; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
right. apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* the live blocks after the call: the new block, the table, the entry's other blocks and the rest *)
Lemma dt_grow_perm : forall ly1 S1 ly2 S2 TB Q e res nc,
Permutation (ablocks B ly1 S1) (TB :: aentry_blks e ++ Q) ->
(re_cap e = 0 -> re_buf e = 0) -> (re_cap e <> 0 -> re_buf e <> 0) ->
(re_buf e = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e, re_cap e) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
Permutation (ablocks B ly2 S2) ((res, nc) :: TB :: dt_hkb e ++ Q).
Proof.
intros ly1 S1 ly2 S2 TB Q e res nc HP Hz Hnz HA HB'.
change (aentry_blks e) with ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++ dt_hkb e) in HP.
revert HP. destruct (re_cap e =? 0) eqn:Ec; intros HP; cbn [app] in HP.
- apply Z.eqb_eq in Ec. eapply Permutation_trans; [exact (HA (Hz Ec))|]. apply perm_skip. exact HP.
- apply Z.eqb_neq in Ec. destruct (HB' (Hnz Ec)) as (l1 & l2 & E1 & P2).
  eapply Permutation_trans; [exact P2|]. apply perm_skip.
  apply (Permutation_cons_inv (a := (re_buf e, re_cap e))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- E1.
  eapply Permutation_trans; [exact HP|]. apply perm_swap.
Qed.

(* the live bytes after the call: at most nc more *)
Lemma dt_grow_bb : forall ly1 S1 ly2 S2 e res nc,
0 <= re_cap e ->
(re_buf e = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e, re_cap e) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
blocks_bytes S2 <= blocks_bytes S1 + nc.
Proof.
intros ly1 S1 ly2 S2 e res nc Hc HA HB'.
rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2).
destruct (Z.eq_dec (re_buf e) 0) as [Hz|Hz].
- rewrite (bsum_perm _ _ (HA Hz)), bsum_cons. cbn [snd]. lia.
- destruct (HB' Hz) as (l1 & l2 & E1 & P2). rewrite (bsum_perm _ _ P2), E1, bsum_cons, !bsum_app, bsum_cons.
  cbn [snd]. lia.
Qed.

(* C3: the live bytes after the call, exactly: the old buffer (re_cap e bytes; none when re_buf e = 0) replaced by
   the nc-byte block *)
Lemma dt_grow_bbx : forall ly1 S1 ly2 S2 e res nc,
(re_buf e = 0 -> re_cap e = 0) ->
(re_buf e = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e, re_cap e) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
blocks_bytes S2 = blocks_bytes S1 - re_cap e + nc.
Proof.
intros ly1 S1 ly2 S2 e res nc H0 HA HB'.
rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2).
destruct (Z.eq_dec (re_buf e) 0) as [Hz|Hz].
- rewrite (bsum_perm _ _ (HA Hz)), bsum_cons, (H0 Hz). cbn [snd]. lia.
- destruct (HB' Hz) as (l1 & l2 & E1 & P2). rewrite (bsum_perm _ _ P2), E1, bsum_cons, !bsum_app, bsum_cons.
  cbn [snd]. lia.
Qed.

(* the meter after the growth's request (C3: the live bytes after it plus the peak of the rest, from dt_grow_pk and
   dt_grow_bbx at the call site) *)
Lemma dt_grow_bud : forall cx S1 S2 spent tl tl2 (EV : dtrace) nc,
dbud MT MMAX cx S1 spent tl -> tl = EV ++ tl2 ->
tr_cost MT EV = mo_malloc MT nc + mo_free MT -> tr_max EV = nc ->
0 <= mo_malloc MT nc + mo_free MT ->
mo_le MT S1 S2 (mo_malloc MT nc + mo_free MT) ->
blocks_bytes S2 + tr_peak tl2 <= LIVE_MAX ->
dbud MT MMAX cx S2 (spent + (mo_malloc MT nc + mo_free MT)) tl2.
Proof.
intros cx S1 S2 spent tl tl2 EV nc (Hle & Hsp & Hcost & Hlv & Hmax) Etl Hc Hm Hc0 HMO HBB.
rewrite Etl, dt_tr_cost_app, Hc in Hcost.
rewrite Etl, dt_tr_max_app, Hm in Hmax.
split; [exact (mle_station MT (dxS cx) S1 S2 spent _ MTL Hle HMO)|].
split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* The memory core of DT1 after the call and the two stores, from realloc #1's post (on mem2) and what the
   stretch 0x8324c .. 0x8326c leaves (m3: every byte but s->buf and s->cap as the call left it, presence grown,
   s->buf = res, s->cap = nc).  The entry becomes dt_ge e1 res nc junk: the buffer is the new block, its first
   cap bytes the copy of the old buffer's U ++ junk, the rest of it the block's own bytes. *)
Lemma dt_grow_core : forall cx s1 (W1 : world SEGS) ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1
  (W2 : world SEGS) ly2 S2 mem2 md2 m3 md3 res nc,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 sent LB1 ->
DLINK s1 e1 h1 -> re_used e1 <= APARTIAL ->
drain_b_c.ds_cap (dgrow s1) = nc ->
nc = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) -> 8192 <= nc <= 16384 ->
AR SEGS B ly2 S2 W2 mem2 md2 -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) nc ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 m3 md3 (k1 + 3) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W2) mem2 x) ->
(forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) m3 x) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 16) 8 res ->
val_mem SEGS (arm W2 m3) (dxSA cx + 32) 8 nc ->
exists junk,
  DMEM B RG cx ly2 S2 W2 m3 md3 (k1 + 3) (dt_ge e1 res nc junk) h1 (dgrow s1) out1 ev1 sent LB1 /\
  DLINK (dgrow s1) (dt_ge e1 res nc junk) h1.
Proof.
intros cx s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 W2 ly2 S2 mem2 md2 m3 md3 res nc
  HB HMEM HLINK Hused Enc Hncap Hnb HAR2 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ3 KV KP V16 V32.
pose proof asan_consts as (C1 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
pose proof HMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT &
  HLIVE & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (FB : alloc_ceiling + DRAIN_STK <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
assert (AR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (AR3 : AR SEGS B ly2 S2 W2 m3 md3) by (eapply ajournal_gx_AR; exact HJ3).
pose proof HOKX as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HU & Hucap & HBUF & _ & HHP & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (HSAle' : dxSA cx + 56 <= dxG cx + 896) by (clear - HSAle; unfold AENT, ATABLE in HSAle; lia).
assert (Hcn : re_cap e1 <= nc /\ (nc = 8192 \/ nc = 16384)).
{ clear - Hncap Hnb Hcapv. destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq in Hncap; cbn [Z.eqb] in Hncap; lia. }
assert (RQN : req_size nc = nc) by (unfold req_size; destruct (Z.eqb_spec nc 0) as [E0|E0]; [lia | reflexivity]).
(* ---- the live blocks before and after the call ---- *)
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> 4096 <= re_buf e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1)).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ AR1 Hin) as (_ & H4 & _). split; [exact H4 | exact Hin]. }
assert (Hnz' : re_cap e1 <> 0 -> re_buf e1 <> 0) by (intros Hc; destruct (Hnz Hc) as (H4 & _); lia).
pose proof (dt_grow_perm ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res nc HPERM Hz Hnz' HpermA HpermB)
  as P2.
pose (TB := (dxG cx, ATABLE)).
pose (NB := (res, nc)).
pose (R := asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).
pose (Q := dt_hkb e1 ++ R).
change (Permutation (ablocks B ly2 S2) (NB :: TB :: Q)) in P2.
assert (P2T : Permutation (ablocks B ly2 S2) (TB :: NB :: Q))
  by (eapply Permutation_trans; [exact P2 | apply perm_swap]).
assert (P1 : Permutation (ablocks B ly1 S1) (TB :: (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ Q)).
{ eapply Permutation_trans; [exact HPERM|]. apply perm_skip.
  change (aentry_blks e1) with ((if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ dt_hkb e1).
  rewrite <- app_assoc. apply Permutation_refl. }
assert (Q1 : forall b, In b (TB :: Q) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P1)). destruct Hb as [<-|Hb]; [left; reflexivity|].
  right. apply in_or_app. right. exact Hb. }
assert (NB2 : In NB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); left; reflexivity).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2T)); left; reflexivity).
assert (Q2 : forall b, In b Q -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym P2)); right; right; exact Hb).
assert (DNB : forall b, In b (TB :: Q) -> zdisjoint (block_rng NB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head ly2 S2 W2 mem2 md2 NB (TB :: Q) b HAR2 P2 Hb)).
assert (DOB : re_cap e1 <> 0 -> forall b, In b (TB :: Q) ->
  zdisjoint (block_rng (re_buf e1, re_cap e1)) (block_rng b)).
{ intros Hc b Hb. apply (dt_sep_head ly1 S1 W1 m1 md1 _ (TB :: Q) b AR1); [|exact Hb].
  eapply Permutation_trans; [exact P1|]. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [app]. apply perm_swap. }
assert (DTQ : forall b, In b Q -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head ly2 S2 W2 mem2 md2 TB (NB :: Q) b HAR2 P2T (or_intror Hb))).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE AR1 (Q1 TB (or_introl eq_refl)))
  as (_ & HG4096 & HGceil & _).
rewrite RQT in HGceil.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 res nc AR3 NB2) as (_ & HN4 & HNcl & _ & HNpr & _).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 (dxG cx) ATABLE AR3 TB2) as (_ & _ & _ & _ & HTpr & _).
rewrite RQN in HNcl, HNpr. rewrite RQT in HTpr.
(* ---- what the call keeps of the table and the entry's other blocks ---- *)
assert (KC : forall b x, In b (TB :: Q) -> fst b <= x < fst b + req_size (snd b) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) m1 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx. pose proof Hkept2 as (_ & K2 & _).
  replace x with (pb + (x - pb)) by ring. apply (K2 pb mb (x - pb) (Q1 _ Hb)); [lia|].
  replace (pb + (x - pb)) with x by ring. cbv beta.
  intros [Hn | (Hb0 & Ho)].
  - pose proof (DNB _ Hb) as Dj. unfold zdisjoint, block_rng, NB in Dj. cbn [fst snd] in Dj. lia.
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    pose proof (DOB Hc _ Hb) as Dj. unfold zdisjoint, block_rng in Dj. cbn [fst snd] in Dj. lia. }
(* ---- and what the stores keep ---- *)
assert (KO : forall b x, In b Q -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m3 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx.
  pose proof (DTQ _ Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj. rewrite RQT in Dj.
  destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 pb mb AR3 (Q2 _ Hb)) as (_ & H4 & Hcl & _ & Hpr & _).
  assert (Hr : 0 <= x < 2 ^ 64) by lia.
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x Hr N1 N2). exact (KC (pb, mb) x (or_intror Hb) Hx).
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (FK : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64)
    by (clear - Hx FB HAC; unfold DRAIN_STK, SL_STK, SL_FRAME, DRAIN_FRAME, ASTACK in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x ltac:(lia) N1 N2). exact (K1 x Hr1 Hr2).
  - intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
    intros Hp. apply KP. exact (K5 x Hr1 Hr2 Hp). }
assert (NIMG : forall x, in_img SEGS x ->
  ~ (dxSA cx + 16 <= x < dxSA cx + 24) /\ ~ (dxSA cx + 32 <= x < dxSA cx + 40)).
{ intros x Hx. split; intros Hw;
    exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE x AR1 (Q1 TB (or_introl eq_refl))
      ltac:(rewrite RQT; lia) Hx). }
assert (APK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> apresent (w_H W1) m1 x -> apresent (w_H W2) m3 x).
{ intros x Hi Hno Herr Hp.
  assert (Hnot : forall ly0 S0 (W0 : world SEGS) m0 md0, AR SEGS B ly0 S0 W0 m0 md0 -> ~ aowned B ly0 S0 x)
    by (intros ly0 S0 W0 m0 md0 HA Ho; apply Hno; exact (proj1 (al_owned_image SEGS B LAWS ly0 S0 W0 m0 md0 x HA Hi) Ho)).
  apply KP. apply (Hpres2 x Hi (Hnot _ _ _ _ _ AR1) (Hnot _ _ _ _ _ HAR2) Herr); [|exact Hp].
  intros [Hn | (Hb0 & Ho)].
  - exact (blk_img SEGS B LAWS ly2 S2 W2 mem2 md2 res nc x HAR2 NB2 Hn Hi).
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) x AR1 (proj2 (Hnz Hc)) Ho Hi). }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  assert (Hi : in_img SEGS x) by exact (proj1 (HG x Hg)).
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  assert (EV : aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
  { rewrite (KV x Hr N1 N2). replace x with (as_errno B + (x - as_errno B)) by ring. apply Herr2.
    clear - Hx; lia. }
  split; [exact EV|]. intros _.
  apply dt_img_wr; [exact Hi | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [exact (conj (proj1 (HG x Hx)) (proj1 (proj2 (HG x Hx)))) | exact (conj (proj1 (HGO x Hx)) (proj1 (proj2 (HGO x Hx))))]).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by lia.
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  pose proof Hkept2 as (_ & _ & K3 & _).
  split; [rewrite (KV x Hr N1 N2); exact (K3 x Hi Ho Hne)|].
  intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
  intros Hp. exact (APK x Hi Ho Hne Hp). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
assert (TK : forall x, dxSA cx <= x < dxSA cx + 56 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
  ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. rewrite (KV x ltac:(lia) N1 N2).
  apply (KC TB x (or_introl eq_refl)). unfold TB. cbn [fst snd]. rewrite RQT. lia. }
(* ---- the entry: the new buffer, its bytes and the 56 bytes at SA ---- *)
assert (CP3 : 0 < re_cap e1 -> forall i, 0 <= i < re_cap e1 ->
  aview SEGS (w_H W2) m3 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)).
{ intros Hc i Hi.
  pose proof (DNB TB (or_introl eq_refl)) as Dj. unfold zdisjoint, block_rng, NB, TB in Dj. cbn [fst snd] in Dj.
  rewrite RQT, RQN in Dj.
  rewrite (KV (res + i) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Hcopy; [destruct (Hnz ltac:(lia)) as (H4 & _); lia | rewrite Z.min_l by lia; exact Hi]. }
assert (HBUF' : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (destruct HBUF as [Hq|(Hq1 & _ & Hq3 & Hq4)]; [left; exact Hq | right; exact (conj Hq1 (conj Hq3 Hq4))]).
assert (Hcb : 0 <= re_cap e1 <= nc) by (destruct Hcapv as [Hq|[Hq|Hq]]; lia).
destruct (dt_newbuf W1 m1 W2 m3 e1 res nc HBUF' HU Hcb CP3 (fun x Hx => proj1 (HNpr x Hx)))
  as (junk & Hjl & Hjg).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
assert (Hnc64 : 0 <= nc < 2 ^ 64) by lia.
assert (ENT3 : garr8 SEGS (arm W2 m3) (dxSA cx) (bzs (entry_bytes (dt_ge e1 res nc junk)))).
{ apply (dt_entry_grow W1 m1 W2 m3 (dxSA cx) e1 res nc junk Hp1 Hres64 Hnc64 HENTB V16 V32); [| | | exact Hp2];
    intros x Hx; apply TK; lia. }
assert (AWR3 : awr W2 m3 (dxSA cx) AENT).
{ intros i Hi. apply (apresent_writable SEGS).
  apply (proj1 (HTpr (dxSA cx + i) ltac:(unfold AENT in Hi; lia))). }
assert (AK : akept W1 m1 W2 m3 (gfp (re_hp e1) (bzs (key_ptrs (re_keys e1))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e1))).
{ intros r Hr x Hx. destruct Hr as [<- | Hr].
  - unfold gfp in Hx. cbn [fst snd] in Hx. rewrite dt_bzs_len, dt_key_ptrs_len in Hx.
    destruct HHP as [(Hz0 & Hk0) | (Hz0 & HinH & Hk1 & Hk2 & _)].
    + rewrite Hk0 in Hx. cbn [length] in Hx. lia.
    + apply (KO (re_hp e1, re_kh e1) x).
      * unfold Q, dt_hkb. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz0).
        apply in_or_app. left. left. reflexivity.
      * cbn [fst snd]. unfold re_nheld in Hk1. pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & RQ). lia.
  - apply in_map_iff in Hr as (k & <- & Hk).
    apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
    + unfold Q, dt_hkb. apply in_or_app. left. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    + unfold gfp in Hx. cbn [fst snd] in Hx |- *. rewrite dt_bzs_len, length_app in Hx. cbn [length] in Hx.
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & RQ). lia. }
assert (OKX3 : aentry_okx B ly2 S2 W2 m3 (dt_ge e1 res nc junk)).
{ apply (dt_aentry_okx_grow ly1 S1 W1 m1 ly2 S2 W2 m3 e1 res nc junk HOKX (proj2 Hcn)
    ltac:(unfold APARTIAL in Hused; lia) NB2 Hjl Hjg AK).
  intros b Hb. apply Q2. unfold Q. apply in_or_app. left. exact Hb. }
(* ---- the harness source, the other slots, g_s, the output ---- *)
assert (SRC3 : asrc_at B ly2 S2 W2 m3 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m3 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. destruct (dt_src_fp ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. unfold Q, R. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - intros b Hb. apply Q2. unfold Q, R. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (OTH3 : aothers_at RG W2 m3 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & Va & Vb & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m3) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact Va] | split; [apply GV; [| | exact Vb] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK3 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m3 x)
  by (intros x H1 H2; exact (dt_bk_trans _ _ W1 m1 W2 m3 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT3 : aout_at B RG ly2 S2 W2 m3 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m3 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct (dt_out_fp _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, drain_b_c.ds_ocap s1) x).
    + unfold Q, R. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply Q2. unfold Q, R. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (ROM3 : rom_view SEGS W2 m3).
{ intros x Hx. destruct (HROMO x Hx) as (_ & Hpin & Hne & _).
  destruct (Exists_dec (in_zr x) (as_owned_static B) (dt_in_zr_dec x)) as [Hown | Hno].
  - eapply rom_pinned_view; [exact AR3 | exact (Hpin Hown)].
  - assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    destruct (NIMG x Hi) as (N1 & N2).
    assert (Hr : 0 <= x < 2 ^ 64)
      by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
    pose proof Hkept2 as (_ & _ & K3 & _).
    rewrite (KV x Hr N1 N2), (K3 x Hi Hno Hne). exact (HROM x Hx). }
assert (PK3 : apres_kept B (dxW cx) (dxmem cx) W2 m3)
  by (intros x Hi Ho He Hp; exact (APK x Hi Ho He (HPRESK x Hi Ho He Hp))).
assert (EA2 : aentry_blks (dt_ge e1 res nc junk) = NB :: dt_hkb e1).
{ unfold aentry_blks, dt_ge, dt_hkb. cbn [re_cap re_buf re_hp re_kh re_keys].
  rewrite (proj2 (Z.eqb_neq nc 0) ltac:(lia)). reflexivity. }
exists junk. split.
- unfold DMEM.
  refine (conj HJ3 (conj ROM3 (conj PK3 (conj (eq_trans Hfrs2 HFRM) (conj (dt_frame_kept cx W1 m1 W2 m3 FK HFRAME)
    (conj ENT3 (conj AWR3 (conj OKX3 (conj SRC3 (conj OTH3 (conj GSK3 (conj OUT3 (conj HLIVE _))))))))))))).
  rewrite EA2. exact P2T.
- pose proof HLINK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  refine (conj (eq_sym Enc) (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10
    (conj K11 K12))))))))))).
Qed.

(* ---- After realloc #1 returned: the two stores and the cut DT1. ----
   What the rule's post gives (the new block res of n bytes in place of the old one, the copy of the first
   min(n0, n) bytes, acall_kept over everything else, the meter step) and what the stretch 0x8324c .. 0x8326c
   must still do: the `beqz a0` the forced success kills, the shadow checks of &s->buf and &s->cap, the two
   stores, and then DT1 of the grown state with the entry's buf / cap replaced -- its aentry_okx over the new
   block (the junk beyond the copy comes from the block's presence), the Permutation with the new block, the
   meter as spent + mo_malloc n + mo_free, and dlater of the grown state by dt_grow_tr. *)
Lemma dt_grow_post : forall cx s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl
  memS (W2 : world SEGS) ly2 S2 regs2 mem2 md2 res tl2,
DBASE B MT MMAX RG cx ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 8 = w64 ((rg_s RG + 4) / 8) -> getr regs1 9 = w64 (rg_s RG / 8) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 18 = w64 (rg_s RG) -> getr regs1 19 = w64 384 ->
getr regs1 20 = w64 (drain_b_c.ds_cap (dgrow s1)) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 23 = w64 (shadow_addr (dxSA cx + 32)) ->
getr regs1 24 = w64 (shadow_addr (dxSA cx)) -> getr regs1 25 = w64 (dxSA cx + 32) ->
getr regs1 26 = w64 (dxSA cx + 16) -> getr regs1 27 = w64 (dxSA cx + 24) ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud MT MMAX cx S1 spent tl ->
4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1) ->
drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) ->
8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384 ->
tl = fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)) ++ tl2 ->
dlater cx (dgrow s1)
  (jb + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa))))
  (agrow s1 jb aa) tl2 ->
0 <= DRAIN_STK -> gagree (G_DR B RG) (w_H (dxW cx)) (dxmem cx) memS ->
ajournal SEGS B DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS (dxmd cx) []
  ly2 S2 W2 mem2 md2 (k1 + 3) ->
aregs_preserved regs1 regs2 -> getr regs2 10 = w64 res -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2)
   ((res, drain_b_c.ds_cap (dgrow s1)) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, drain_b_c.ds_cap (dgrow s1)) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
            (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
mo_le MT S1 S2 (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
      (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
(forall W3 c3, DT1 cx (dgrow s1) D W3 c3 -> SRr SEGS W3 c3 (dPOST B MT RG cx)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)) md2) (dPOST B MT RG cx).
Proof.
intros cx s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS W2 ly2 S2 regs2 mem2 md2 res tl2
  HB Hsp Hra R3 R4 R8 R9 R10 R11 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2i HPR Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 Herr2 Hpres2 K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16848) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HAR2 : AR SEGS B ly2 S2 W2 mem2 md2) by exact (proj1 HJ2i).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR1 HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
(* the blocks after the call: the table is still live, the new block is (res, nc) *)
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HUl & Hucap & HBUF & _).
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> re_buf e1 <> 0).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hin) as (_ & H4 & _). lia. }
pose proof (dt_grow_perm ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res (drain_b_c.ds_cap (dgrow s1))
  Hperm Hz Hnz HpermA HpermB) as HP2.
assert (TB2 : In (dxG cx, ATABLE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); right; left; reflexivity).
assert (NB2 : In (res, drain_b_c.ds_cap (dgrow s1)) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 NB2) as (_ & _ & HNcl & _).
pose proof (req_size_pos (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)) as (_ & RQN).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (dxG cx) ATABLE HAR2 TB2) as (_ & _ & _ & _ & HTP2 & _).
(* the frame across the call: realloc keeps every byte above its stack window *)
assert (FK0 : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 mem2 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64) by (clear - Hx HspA HspB; unfold DRAIN_FRAME in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  split; [exact (K1 x Hr1 Hr2)|]. intros Hw.
  apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 mem2 x); [|exact Hw]. exact (K5 x Hr1 Hr2). }
pose proof (dt_frame_kept cx W1 m1 W2 mem2 FK0 HFR) as HFR2.
pose proof HFR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F216' & _).
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
{ intros r Hr. pose proof (HPR (bv_unsigned r) Hr) as Q. rewrite Z_to_bv_bv_unsigned in Q. exact Q. }
assert (P2 : getr regs2 2 = getr regs1 2) by (apply PR; dt_cs).
assert (P8 : getr regs2 8 = getr regs1 8) by (apply PR; dt_cs).
assert (P9 : getr regs2 9 = getr regs1 9) by (apply PR; dt_cs).
assert (P18 : getr regs2 18 = getr regs1 18) by (apply PR; dt_cs).
assert (P21 : getr regs2 21 = getr regs1 21) by (apply PR; dt_cs).
assert (P22 : getr regs2 22 = getr regs1 22) by (apply PR; dt_cs).
assert (P23 : getr regs2 23 = getr regs1 23) by (apply PR; dt_cs).
assert (P24 : getr regs2 24 = getr regs1 24) by (apply PR; dt_cs).
assert (P25 : getr regs2 25 = getr regs1 25) by (apply PR; dt_cs).
assert (P26 : getr regs2 26 = getr regs1 26) by (apply PR; dt_cs).
assert (P27 : getr regs2 27 = getr regs1 27) by (apply PR; dt_cs).
assert (P3 : getr regs2 3 = getr regs1 3) by (apply PR; dt_cs).
assert (P4 : getr regs2 4 = getr regs1 4) by (apply PR; dt_cs).
assert (P19 : getr regs2 19 = getr regs1 19) by (apply PR; dt_cs).
assert (P20 : getr regs2 20 = getr regs1 20) by (apply PR; dt_cs).
unfold w64.
remember (Eimg (Ereg regs2 (dt_gp_extra (dxSA cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ n r Hr)).
assert (E2 : ew E 2 = getr regs2 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs2 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs2 4) by (apply EREG; [lia | reflexivity]).
assert (E19 : ew E 19 = getr regs2 19) by (apply EREG; [lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 (drain_b_c.ds_cap (dgrow s1)))
  by (rewrite (EREG 20%nat 20%bv) by (first [lia | reflexivity]); rewrite P20; exact R20).
assert (E10 : ew E 10 = Z_to_bv 64 res)
  by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact Hres10).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); rewrite P18; exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite P21; exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2, P2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (R22' : getr regs2 22 = sv_denot E (SOff 32 0))
  by (rewrite P22, (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs2 25 = sv_denot E (SOff 32 32))
  by (rewrite P25, (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs2 26 = sv_denot E (SOff 32 16))
  by (rewrite P26, (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs2 27 = sv_denot E (SOff 32 24))
  by (rewrite P27, (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs2 23 = sv_denot E (dt_sh 32 32))
  by (rewrite P23, (dt_den_sh E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs2 24 = sv_denot E (dt_sh 32 0))
  by (rewrite P24, (dt_den_sh E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs2 9 = sv_denot E (dt_gv 0))
  by (rewrite P9, (dt_den_gv E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs2 8 = sv_denot E (dt_gv 4))
  by (rewrite P8, (dt_den_gv E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_gp
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gp. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gp_frame, dt_gp_buf, dt_gp_cap;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
        [ exact (dt_den_sh E 32 (dxSA cx) 16 E32 E21 ltac:(lia) ltac:(lia))
        | unfold shadow_addr, SHADOW_OFF;
          (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                  | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia); zside])
        | zside
        | exact F216' ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
  - apply pairwise_disjoint_of_extents. unfold dt_gp_frame, dt_gp_buf, dt_gp_cap, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gp_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W2) mem2)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub ly2 S2 W2 mem2 md2 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR2 TB2).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
pose proof (dt_gx_close (G_DR B RG) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 3) memS HSTK HAG HJ2i) as HJ2.
psrr_branch_tok RUN BR HS SHOK DBspan.
- (* beqz a0 taken: res = 0, but the rule's res is at least 4096 *)
  exfalso. rewrite (dt_beqz_atom E 10 res E10 Hres64) in Hc. apply Z.eqb_eq in Hc. lia.
- paj_run_to_tok RUNTO HS HJ2 SHOK DBspan A_dr_mid.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa0 Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_nil. }
  rewrite ?wvb_collapse in HJ2.
  (* the stretch wrote s->buf and s->cap only, and kept every byte's presence *)
  assert (Hnw : forall x, ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
    ~ in_wrange E (ss_mem ss_gp) x).
  { intros x N1 N2 (r & Hin & Hr). cbv [ss_mem ss_gp dt_gp_frame dt_gp_buf dt_gp_cap] in Hin.
    destruct Hin as [Hq|[Hq|[Hq|[]]]]; subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?U32 in Hr; lia. }
  assert (KV : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
    ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W2) mem2 x)
    by (intros x Hx N1 N2; exact (aview_kept_out E _ (w_H W2) mem2 (ms_mem ms) HFr x Hx (Hnw x N1 N2))).
  assert (KP : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem ms) x)
    by (intros x Hx; exact (apresent_grows _ _ _ _ HG0 Hx)).
  (* the two stored cells *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RB.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RC.
  cbn [ms_mem restrict] in RB, RC.
  assert (V16 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 16) 8 res).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 16 8%N (SOff 10 0) res RB U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 10 res E10 Hres64).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V32 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 32) 8 (drain_b_c.ds_cap (dgrow s1))).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 32 8%N (SOff 20 0) (drain_b_c.ds_cap (dgrow s1))
      RC U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 20 (drain_b_c.ds_cap (dgrow s1)) E20 ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
  dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (18%bv : bv 5) X18.
  dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21. dt_reg HS (22%bv : bv 5) X22.
  dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
  dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
  pmkst HS.
  (* the model side: the growth's request and the meter *)
  pose proof HLINK as (Lcap & Lu & Lrest).
  assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUl).
  destruct (dt_grow_ev (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
    ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
  change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
  assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
  { pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)).
    pose proof (mo_free_nonneg MT MTL). lia. }
  assert (Hb0 : re_buf e1 = 0 -> re_cap e1 = 0)
    by (intros Hb; destruct (Z.eq_dec (re_cap e1) 0) as [Hq|Hq]; [exact Hq | exfalso; exact (Hnz Hq Hb)]).
  pose proof (dt_grow_bbx ly1 S1 ly2 S2 e1 res (drain_b_c.ds_cap (dgrow s1)) Hb0 HpermA HpermB) as HBB.
  assert (HBB2 : blocks_bytes S2 + tr_peak tl2 <= LIVE_MAX).
  { pose proof Hbud as (_ & _ & _ & Hlv & _). rewrite Htl in Hlv.
    destruct (dt_grow_pk (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
      ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlv) as (_ & Hpk).
    change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hpk.
    rewrite <- Lcap in Hpk. lia. }
  pose proof (dt_grow_bud cx S1 S2 spent tl tl2 _ (drain_b_c.ds_cap (dgrow s1)) Hbud Htl Hev_co Hev_max
    HmoN Hmle2 HBB2) as HBUD2.
  (* the memory core *)
  destruct (dt_grow_core cx s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 W2 ly2 S2 mem2 md2
    (ms_mem ms) _ res (drain_b_c.ds_cap (dgrow s1)) HB HMEM HLINK Hused eq_refl Hncap Hnb HAR2 Hfrs2 Hres4096
    HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ2 KV KP V16 V32) as (junk & HDM & HDL).
  (* the cut *)
  apply K. unfold DT1.
  eexists _, ly2, S2, _, _, (k1 + 3), (dt_ge e1 res (drain_b_c.ds_cap (dgrow s1)) junk), h1, out1, ev1, LB1,
    (spent + (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT)), _, (agrow s1 jb aa), tl2.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2), P2; exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3), P3; exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4), P4; exact R4|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') (eq_trans P22 R22))|].
    split; [rewrite X25; exact (eq_trans (eq_sym R25') (eq_trans P25 R25))|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') (eq_trans P27 R27))|].
    split; [rewrite X26; exact (eq_trans (eq_sym R26') (eq_trans P26 R26))|].
    split; [rewrite X18, (dt_den_reg E 18 _ E18); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') (eq_trans P9 R9))|].
    split; [rewrite X8; exact (eq_trans (eq_sym R8') (eq_trans P8 R8))|].
    split; [rewrite X21, (dt_den_reg E 21 _ E21); reflexivity|].
    split; [rewrite X23; exact (eq_trans (eq_sym R23') (eq_trans P23 R23))
           |rewrite X24; exact (eq_trans (eq_sym R24') (eq_trans P24 R24))]. }
  split; [rewrite X19, (dt_den_reg E 19 _ E19), P19; exact R19|].
  split; [exact HDM|].
  split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HDL|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
  split; [exact Hlater2 | exact HBUD2].
Qed.

(* The walk from the trampoline: realloc #1 itself and the two stores it feeds.  Stated over the registers and
   the memory core the stretch leaves at the trampoline, so that both capacity arms share it; DI of the round
   head gives the signs that bound what the later rounds still owe (dt_later_meters). *)
Lemma dt_grow_after : forall cx s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl c0,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c0 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 8 = w64 ((rg_s RG + 4) / 8) -> getr regs1 9 = w64 (rg_s RG / 8) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 18 = w64 (rg_s RG) -> getr regs1 19 = w64 384 ->
getr regs1 20 = w64 (drain_b_c.ds_cap (dgrow s1)) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 23 = w64 (shadow_addr (dxSA cx + 32)) ->
getr regs1 24 = w64 (shadow_addr (dxSA cx)) -> getr regs1 25 = w64 (dxSA cx + 32) ->
getr regs1 26 = w64 (dxSA cx + 16) -> getr regs1 27 = w64 (dxSA cx + 24) ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud MT MMAX cx S1 spent tl ->
(forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (SIGMA WS_realloc)) m1 (seg_rom SEGS)) md1) (dPOST B MT RG cx).
Proof.
intros cx s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl c0 HB HDI
  Hsp Hra R3 R4 R8 R9 R10 R11 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & Hgarr0 & Hawr0 & HEOK0 & Hj4 & Hsrc0 & Hoth0 & HfdB &
  Hskip0 & HU0 & Hout0 & Hrom0 & Hperm0 & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16848) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hcapv : re_cap e1 = 0 \/ re_cap e1 = 8192 \/ re_cap e1 = 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); lia).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hroom : 4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1)).
{ apply dt_grow_room; [exact Hlt | rewrite Hulen; unfold APARTIAL in Hused |- *; lia
  | rewrite Hulen, <- Lcap; exact Hucap | rewrite <- Lcap; exact Hcapv ]. }
assert (Hncap : drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2)).
{ change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
  rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; exact Hucap) Hlt),
    <- Lcap. reflexivity. }
assert (Hnb : 8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384)
  by (rewrite Hncap; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; cbn [Z.eqb];
      [lia | lia | unfold APARTIAL in Hused; lia]).
(* what the growth asks of the allocator *)
destruct (dt_grow_tr cx s1 jb aa tl Hlater Hroom) as (tl2 & Htl & Hlater2).
destruct (dt_later_meters cx s1 D W1 c0 _ _ tl2 HB HDI (or_introl Hlater2)) as (_ & Hco2).
destruct (dt_grow_ev (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
  ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
pose proof Hbud as (Hmle & Hspent & Hcost & Hlive & Hmax).
rewrite Htl, dt_tr_max_app, Hev_max in Hmax.
rewrite Htl in Hlive.
destruct (dt_grow_pk (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
  ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlive) as (Hlv1 & _).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hlv1.
rewrite Htl, dt_tr_cost_app, Hev_co in Hcost.
assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
{ pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)).
  pose proof (mo_free_nonneg MT MTL). lia. }
(* the buffer the round hands over *)
assert (Hbufc : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\
   Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hpn : re_buf e1 = 0 \/ In (re_buf e1, re_cap e1) (ablocks B ly1 S1))
  by (destruct Hbufc as [(_ & Hq & _)|(_ & Hq & _)]; [left; exact Hq | right; exact Hq]).
destruct (dt_gx_open (G_DR B RG) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W1 m1 md1 k1 HJ) as (memS & HSTK & HAG & HJi).
eapply SRr_bind.
{ eapply (AREALLOC W1 regs1 m1 DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS (dxmd cx) []
    ly1 S1 md1 k1 (re_buf e1) (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) (- DRAIN_FRAME)
    (w64 (BASE + A_dr_rret)) [] HJi).
  - exact Hpn.
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - unfold DRAIN_FRAME in *. lia.
  - reflexivity.
  - unfold DRAIN_FRAME. lia.
  - assert (Hq : ASTACK - - DRAIN_FRAME <= DRAIN_STK) by (vm_compute; discriminate). exact Hq.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact Hra.
  - unfold w64. apply ret_ok_codeptr_v; [unfold A_dr_rret, AF_fr_drain; lia
    | unfold A_dr_rret, AF_fr_drain; reflexivity].
  - apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] regs1).
    + apply achain_low. assert (Hq : (rg_s RG + 4) / 8 <= rg_s RG + 4) by (apply Z.div_le_upper_bound; lia).
      lia.
    + unfold DRAIN_FRAME in *. lia.
    + unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
      assert (Hq : (rg_s RG + 4) / 8 <= rg_s RG + 4) by (apply Z.div_le_upper_bound; lia).
      assert (Hq2 : 0 <= (rg_s RG + 4) / 8) by (apply Z.div_pos; lia). lia.
    + unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small
        by (unfold A_dr_rret, AF_fr_drain; lia). unfold A_dr_rret, AF_fr_drain. lia.
  - intros Hp0 Hin0 i Hi.
    assert (Hcap0 : 0 < re_cap e1)
      by (destruct Hbufc as [(_ & Hq & _)|(Hq & _)]; [contradiction | lia]).
    assert (Hinbl : In (re_buf e1, re_cap e1) (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1)).
    { apply in_or_app. left. unfold aentry_blks.
      assert (Ec : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Ec. left. reflexivity. }
    apply (dt_buf_fp cx ly1 S1 W1 m1 md1 (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1) (re_buf e1) (re_cap e1) HAR);
      [ (try rewrite <- !app_assoc); exact Hperm | exact Hinbl
      | (try rewrite <- !app_assoc); exact Hperm0 | exact Hin0 | lia
      | unfold ATABLE; lia | exact Hi ].
  - apply (dt_mo_ok_of cx S1 spent tl);
      [ exact (proj2 (proj2 (proj2 (proj2 (proj2 HBrest))))) | exact Hbud | exact HmoN|].
    rewrite Htl, dt_tr_cost_app, Hev_co. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2 & HJ2 & Hpres' & Hres10 & Hfrs2 &
  Hres4096 & HpermA & HpermB & Hcopy & Hkept2 & Hmle2 & Herr2 & Hpres2).
subst c2.
exact (dt_grow_post cx s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS
  W2 ly2 S2 regs2 mem2 md2 res tl2 HB Hsp Hra R3 R4 R8 R9 R10 R11 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2 Hpres' Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 Herr2 Hpres2 K).
Qed.

Lemma dt_grow : forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
(forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx s1 D W1 c1 HB HDI Hlt K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDI as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 &
  F224 & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16848) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & Hq & _); exact Hq).
assert (Hcapb : 0 <= re_cap e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hl & _); lia).
assert (Hbufb : 0 <= re_buf e1 /\ re_buf e1 + re_cap e1 <= alloc_ceiling).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _).
  destruct Hq as [(Hc & Hb & Hu)|(Hc & Hin & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hin) as (_ & H4 & Hcl & _).
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq). lia. }
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_gr_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs1 25 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs1 26 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs1 23 = sv_denot E (dt_sh 32 32))
  by (rewrite (dt_den_sh E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs1 24 = sv_denot E (dt_sh 32 0))
  by (rewrite (dt_den_sh E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite (dt_den_gv E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs1 8 = sv_denot E (dt_gv 4))
  by (rewrite (dt_den_gv E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_gr
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gr. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gr_frame, dt_gr_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact (dt_den_sh E 32 (dxSA cx) 16 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact (dt_den_sh E 32 (dxSA cx) 24 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F224 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 35 0) (re_buf e1));
          [exact (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_buf W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_cap W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_gr_frame, dt_gr_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gr_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUN BR HS SHOK DBspan.
- (* 4096 <= cap - used: not this arm *)
  rewrite (dt_bnez_room E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_le in Hc. rewrite <- Lcap, Hulen in Hlt. lia.
- paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  match type of HS with st_ok_pi _ _ _ ?ss _ => let p := eval vm_compute in (ss_pc ss) in idtac "GRW-PC:" p end.
  psrr_branch_tok RUN BR HS SHOK DBspan.
  all: rewrite (dt_bnez_atom E 33 (re_cap e1) E33 ltac:(lia)) in Hc0.
  + (* the entry has a buffer: the round asks for twice its capacity *)
    apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = re_cap e1 * 2).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap. apply Z.eqb_neq in Hc0. rewrite Hc0. reflexivity. }
    dt_reg HS (1%bv : bv 5) X1. dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3.
    dt_reg HS (4%bv : bv 5) X4. dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9.
    dt_reg HS (10%bv : bv 5) X10. dt_reg HS (11%bv : bv 5) X11. dt_reg HS (18%bv : bv 5) X18.
    dt_reg HS (19%bv : bv 5) X19. dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
    dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    eapply (dt_grow_after cx s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl _ HB HDI).
    all: first
      [ (unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp)
      | (rewrite X1; change 240%nat with A_TEXT; rewrite (codeptr_val E 3936 HEI);
         unfold w64, A_dr_rret, AF_fr_drain; f_equal; lia)
      | (rewrite X3, (dt_den_reg E 3 _ E3); exact R3)
      | (rewrite X4, (dt_den_reg E 4 _ E4); exact R4)
      | (rewrite X8; exact (eq_trans (eq_sym R8') R8))
      | (rewrite X9; exact (eq_trans (eq_sym R9') R9))
      | (rewrite X10, (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)); reflexivity)
      | (rewrite X11, (dt_den_sll E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc; reflexivity)
      | (rewrite X18, (dt_den_reg E 18 _ E18); reflexivity)
      | (rewrite X19; cbn [sv_denot]; reflexivity)
      | (rewrite X20, (dt_den_sll E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc; reflexivity)
      | (rewrite X21, (dt_den_reg E 21 _ E21); reflexivity)
      | (rewrite X22; exact (eq_trans (eq_sym R22') R22))
      | (rewrite X23; exact (eq_trans (eq_sym R23') R23))
      | (rewrite X24; exact (eq_trans (eq_sym R24') R24))
      | (rewrite X25; exact (eq_trans (eq_sym R25') R25))
      | (rewrite X26; exact (eq_trans (eq_sym R26') R26))
      | (rewrite X27; exact (eq_trans (eq_sym R27') R27))
      | exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
          (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      | exact HnoNUL | exact Hused | exact HLINK | exact HSAME | exact HHIST | exact HJ1
      | exact Hlt | exact Hlater | exact Hbud | exact K ].
  + (* no buffer yet: the round asks for 8192 *)
    apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = 8192).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap, Hc0. reflexivity. }
    dt_reg HS (1%bv : bv 5) X1. dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3.
    dt_reg HS (4%bv : bv 5) X4. dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9.
    dt_reg HS (10%bv : bv 5) X10. dt_reg HS (11%bv : bv 5) X11. dt_reg HS (18%bv : bv 5) X18.
    dt_reg HS (19%bv : bv 5) X19. dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
    dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    eapply (dt_grow_after cx s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl _ HB HDI).
    all: first
      [ (unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp)
      | (rewrite X1; change 240%nat with A_TEXT; rewrite (codeptr_val E 3936 HEI);
         unfold w64, A_dr_rret, AF_fr_drain; f_equal; lia)
      | (rewrite X3, (dt_den_reg E 3 _ E3); exact R3)
      | (rewrite X4, (dt_den_reg E 4 _ E4); exact R4)
      | (rewrite X8; exact (eq_trans (eq_sym R8') R8))
      | (rewrite X9; exact (eq_trans (eq_sym R9') R9))
      | (rewrite X10, (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)); reflexivity)
      | (rewrite X11, Hnc; cbn [sv_denot]; reflexivity)
      | (rewrite X18, (dt_den_reg E 18 _ E18); reflexivity)
      | (rewrite X19; cbn [sv_denot]; reflexivity)
      | (rewrite X20, Hnc; cbn [sv_denot]; reflexivity)
      | (rewrite X21, (dt_den_reg E 21 _ E21); reflexivity)
      | (rewrite X22; exact (eq_trans (eq_sym R22') R22))
      | (rewrite X23; exact (eq_trans (eq_sym R23') R23))
      | (rewrite X24; exact (eq_trans (eq_sym R24') R24))
      | (rewrite X25; exact (eq_trans (eq_sym R25') R25))
      | (rewrite X26; exact (eq_trans (eq_sym R26') R26))
      | (rewrite X27; exact (eq_trans (eq_sym R27') R27))
      | exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
          (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      | exact HnoNUL | exact Hused | exact HLINK | exact HSAME | exact HHIST | exact HJ1
      | exact Hlt | exact Hlater | exact Hbud | exact K ].
Qed.

(* ---- The symbolic state at DT1 (0x8326c) for source_of's scan. ----
   Atoms beside 18 = g_s and 21 = SHADOW_OFF: 32 = SA, 33 = s->cap, 34 = s->used, 35 = s->buf,
   36 = s->fd, and the four slots of g_s as (fd, open) pairs: 37 / 38, 39 / 40, 41 / 42, 43 / 44.
   The scan reads g_s[i].open at 96 i + 4 and g_s[i].fd at 96 i; aothers_at kills every slot but j. *)
Definition A_dr_scan : Z := AF_fr_drain + 0x1d8.   (* 0x832b4, the scan loop's head *)
Definition A_dr_shl1 : Z := AF_fr_drain + 0x1dc.   (* 0x832b8, the shadow load of &g_s[i].open *)
Definition A_dr_shl2 : Z := AF_fr_drain + 0x1f4.   (* 0x832d0, the shadow load of &g_s[i].fd *)
Definition dt_sc_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 336 0 0
  [ YP09.mkChunk 216 (dt_shA 32 16); YP09.mkChunk 224 (dt_shA 32 24) ].
Definition dt_sc_sa : YP09.region := YP09.mkRegion (Some 32%nat) 0 56 0 0
  [ YP09.mkChunk 0 (CVal 4 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
    YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)) ].
Definition dt_gs_chunks : list YP09.chunk :=
  [ YP09.mkChunk 0 (CVal 4 (SOff 37 0)); YP09.mkChunk 4 (CVal 4 (SOff 38 0));
    YP09.mkChunk 96 (CVal 4 (SOff 39 0)); YP09.mkChunk 100 (CVal 4 (SOff 40 0));
    YP09.mkChunk 192 (CVal 4 (SOff 41 0)); YP09.mkChunk 196 (CVal 4 (SOff 42 0));
    YP09.mkChunk 288 (CVal 4 (SOff 43 0)); YP09.mkChunk 292 (CVal 4 (SOff 44 0)) ].
Definition dt_sc_gs : YP09.region := YP09.mkRegion (Some 18%nat) 0 384 0 0 dt_gs_chunks.
Definition dt_sc_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0); (18%nat, dt_IMGF);
    (32%nat, dt_HEAPF); (33%nat, mkAF 0 16384 0); (34%nat, mkAF 0 16384 0) ] [] [].
Definition ss_sc : sstate :=
  mkSS A_dr_mid (sr_set dt_regs_top 19%bv (SLit 384)) [ dt_sc_frame; dt_sc_sa; dt_sc_gs ] None dt_sc_facts.
Definition SHsc : list shent := [ mkSHE 32 0 56; mkSHE 18 0 384 ].
Definition dt_sc_extra (SA cap used buf fd f0 o0 f1 o1 f2 o2 f3 o3 : Z) : list word :=
  map (Z_to_bv 64) [SA; cap; used; buf; fd; f0; o0; f1; o1; f2; o2; f3; o3].

(* The loop head 0x832b4 after the first i slots were passed over: a2 = 96 i, s8 = the shadow base + 12 i,
   s3 = 0x180, a0 = s->buf + s->used, a3 = s->cap - s->used and a4 = s->fd.  The scan has not yet reached
   the harness's own slot j (i <= j), so every slot passed over was closed or on another fd. *)
Definition DSC (cx : dcx) (sg : drain_b_c.dstate) (D : list Z) (i : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_scan) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 27 = w64 (dxSA cx + 24) /\ getr regs1 26 = w64 (dxSA cx + 16) /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
getr regs1 14 = w64 (re_fd e1) /\ getr regs1 12 = w64 (96 * Z.of_nat i) /\
getr regs1 19 = w64 384 /\ getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat i) /\
(i <= dxj cx)%nat /\
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud MT MMAX cx S1 spent tl.

(* ---- The other three slots, with the values the machine compares. ----
   aothers_at (W_contract.v, a Theorem Labs lane's fix f71593d7630) gives the slot's fd and open as values whose low
   four bytes val_mem pins, and the fd test as `f mod 2 ^ 32 <> fd mod 2 ^ 32`, which is what `beq a1, a4`
   at 0x832dc decides.  The scan's state wants them canonical, and val_mem keeps only v mod 2 ^ (8 n), so the
   canonical witnesses hold just as well. *)
Lemma dt_val_mod : forall m a (n : nat) v,
val_mem SEGS m a n v -> val_mem SEGS m a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof.
intros m a n v H k Hk. rewrite (H k Hk). f_equal. f_equal.
unfold YO0f.le_byte. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma dt_others_canon : forall (W1 : world SEGS) m1 (j : nat) (fd : Z) i,
aothers_at RG W1 m1 j fd -> (i < 4)%nat -> i <> j -> 0 <= fd < 2 ^ 31 ->
exists f o, val_mem SEGS (arm W1 m1) (rg_s RG + ASRC * Z.of_nat i) 4 f /\
            val_mem SEGS (arm W1 m1) (rg_s RG + ASRC * Z.of_nat i + 4) 4 o /\
            0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32 /\ (o = 0 \/ f mod 2 ^ 32 <> fd mod 2 ^ 32).
Proof.
intros W1 m1 j fd i Hoth Hi4 Hne Hfd.
destruct (Hoth i Hi4 Hne) as (f & o & V1 & V2 & Hdis).
exists (f mod 2 ^ 32), (o mod 2 ^ 32).
assert (HM : 2 ^ (8 * Z.of_nat 4) = 2 ^ 32) by reflexivity.
split; [pose proof (dt_val_mod _ _ 4%nat f V1) as Hq; rewrite HM in Hq; exact Hq|].
split; [pose proof (dt_val_mod _ _ 4%nat o V2) as Hq; rewrite HM in Hq; exact Hq|].
split; [apply Z.mod_pos_bound; lia|].
split; [apply Z.mod_pos_bound; lia|].
destruct Hdis as [Hq|Hq]; [left; rewrite Hq; reflexivity | right].
rewrite Z.mod_mod by lia. exact Hq.
Qed.

(* ---- The scan body's own symbolic state at 0x832b4 (slot i). ----
   Every register keeps its own atom except a2 = 96 i and s3 = 0x180 (literals, so that &g_s[i] is
   g_s + 96 i and the loop test is decided); the extras 32 .. 39 are the four slots' (fd, open).
   The two shadow addresses the body computes ((g_s + 4) >> 3 + s8 and g_s >> 3 + s8, s8 = SB + 12 i) are
   re-expressed before their loads as shadow(g_s + 96 i + 4) and shadow(g_s + 96 i) (dt_reseat). *)
Definition dt_dsc_gs : YP09.region := YP09.mkRegion (Some 18%nat) 0 384 0 0
  [ YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0));
    YP09.mkChunk 96 (CVal 4 (SOff 34 0)); YP09.mkChunk 100 (CVal 4 (SOff 35 0));
    YP09.mkChunk 192 (CVal 4 (SOff 36 0)); YP09.mkChunk 196 (CVal 4 (SOff 37 0));
    YP09.mkChunk 288 (CVal 4 (SOff 38 0)); YP09.mkChunk 292 (CVal 4 (SOff 39 0)) ].
Definition dt_dsc_facts : facts := mkFacts [ (21%nat, mkAF SB SB 0); (18%nat, dt_IMGF) ] [] [].
Definition ss_dsc (i : nat) : sstate :=
  mkSS A_dr_scan (sr_set (sr_set sr_atoms 12%bv (SLit (96 * Z.of_nat i))) 19%bv (SLit 384))
    [ dt_dsc_gs ] None dt_dsc_facts.
Definition SHdsc : list shent := [ mkSHE 18 0 384 ].
Definition dt_dsc_extra (f0 o0 f1 o1 f2 o2 f3 o3 : Z) : list word :=
  map (Z_to_bv 64) [f0; o0; f1; o1; f2; o2; f3; o3].

(* a register re-expressed by another symbolic value with the same denotation *)
Lemma dt_reseat : forall E ss ms (r : bv 5) e,
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

(* the 4 * 96 bytes of g_s as the walk's shadow-entry obligation (HGSZ) *)
Lemma dt_shent_azs : forall ly S (W : world SEGS) mem md E (m : nat) q n,
AR SEGS B ly S W mem md -> azs B q n -> U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
0 <= n -> 0x10000 <= q -> q + n <= 0x5fb000 ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m 0 n).
Proof.
intros ly S W mem md E m q n HAR Hz HB Hm Hn Hq1 Hq2.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
split.
- rewrite Z.add_0_r, Z.sub_0_r. exact (azs_range_addressable B LAWS ly S W mem md q n HAR Hz).
- intros a Ha. unfold SHADOW_OFF. lia.
Qed.

(* the scan's shadow address (g_s + c) >> 3 + (SB + 12 i), with g_s 8-aligned and c < 8, is
   shadow(g_s + 96 i + c): the form the engine reads a zero-shadow load from *)
Lemma dt_den_add_sh : forall E (n : nat) g c i,
ew E n = Z_to_bv 64 ((g + c) / 8) -> ew E 24 = Z_to_bv 64 (SHADOW_OFF + 12 * i) ->
ew E 18 = Z_to_bv 64 g -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
g mod 8 = 0 -> 0 <= c < 8 -> 0x10000 <= g -> g + 384 <= 0x5fb000 -> 0 <= i < 4 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff 24 0)) = sv_denot E (dt_sh 18 (96 * i + c)).
Proof.
intros E n g c i Hn H24 H18 H21 Hg8 Hc Hg1 Hg2 Hi.
assert (Hk : g = 8 * (g / 8)) by (pose proof (Z_div_mod_eq_full g 8); lia).
assert (Hgc : (g + c) / 8 = g / 8).
{ rewrite Hk at 1. rewrite Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small c 8) by lia. lia. }
assert (Hgi : (g + (96 * i + c)) / 8 = g / 8 + 12 * i).
{ replace (g + (96 * i + c)) with ((g / 8 + 12 * i) * 8 + c) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small c 8) by lia. lia. }
assert (Hg0 : 0 <= g / 8 <= g) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (denot_lit_U E (SAlu ALU_ADD (SOff n 0) (SOff 24 0))), (denot_lit_U E (dt_sh 18 (96 * i + c))).
f_equal.
rewrite (dt_U_sh E 18 g (96 * i + c) H18 H21) by lia. unfold shadow_addr. rewrite Hgi.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n ((g + c) / 8) Hn) by lia. rewrite (U_atom E 24 (SHADOW_OFF + 12 * i) H24)
  by (unfold SHADOW_OFF; lia).
rewrite Hgc. rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* the scan's two tests on 4-byte fields: g_s[i].open (0x832c8) and g_s[i].fd against s->fd (0x832dc) *)
Lemma dt_beqz_sx : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v Hn Hv. rewrite branch_eq_U. unfold U. rewrite U_sext32'.
assert (HU : bv_unsigned (sv_denot E (SOff n 0)) = v) by exact (U_atom E n v Hn ltac:(lia)).
assert (HL : bv_unsigned (sv_denot E (SLit 0)) = 0) by exact (U_lit E 0 ltac:(lia)).
rewrite HU, HL. destruct (Z.eqb_spec v 0) as [->|Hne].
- rewrite (sx32_small 0) by lia. reflexivity.
- destruct (Z.eqb_spec (sx32 v) 0) as [He|He]; [|reflexivity].
  exfalso. apply (proj1 (sx32_zero_iff_u32 v Hv)) in He. lia.
Qed.
Lemma dt_beq_sx : forall E (n m : nat) v w,
ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w -> 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 ->
branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff m 0)) = (v =? w).
Proof.
intros E n m v w Hn Hm Hv Hw. rewrite branch_eq_U. unfold U. rewrite U_sext32'.
assert (HU : bv_unsigned (sv_denot E (SOff n 0)) = v) by exact (U_atom E n v Hn ltac:(lia)).
assert (HW : bv_unsigned (sv_denot E (SOff m 0)) = w) by exact (U_atom E m w Hm ltac:(lia)).
rewrite HU, HW.
destruct (Z.eqb_spec v w) as [->|Hne].
- rewrite (sx32_small w) by lia. apply Z.eqb_refl.
- apply Z.eqb_neq. intros He. rewrite <- (sx32_small w) in He by lia.
  apply (sx32_inj_u32 v w Hv ltac:(lia)) in He. lia.
Qed.

Lemma dt_scan_step : forall cx sg D i W1 c1,
DBASE B MT MMAX RG cx -> DSC cx sg D i W1 c1 ->
(forall W2 c2, DSC cx sg D (S i) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DT2 B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx sg D i W1 c1 HB HDSC Knext Kfound.
destruct HDSC as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R10 & R13 & R14 & R12 & R19 & R24 &
  Hij & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (Hfdv : 0 <= re_fd e1 < 2 ^ 31) by (pose proof HEOK as (_ & _ & _ & _ & Hq & _); exact Hq).
assert (Hi4 : (i < 4)%nat) by (pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _); lia).
subst c1. unfold cfg_at, w64.
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & Hgarr0 & Hawr0 & HEOK0 & Hj4 & Hsrc0 & Hoth0 & HfdB &
  HBrest).
pose proof HSAME as (Sfd & Seof & Shfd & Shopen & HSrest).
assert (Hfd : hs_fd h1 = re_fd e1) by (rewrite Shfd, HfdB; exact (eq_sym Sfd)).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
(* the four slots of g_s, as the scan reads them *)
assert (Hslot : forall ii, (ii < 4)%nat -> exists f o,
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii) 4 f /\
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii + 4) 4 o /\
  0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32 /\
  (ii = dxj cx -> f = re_fd e1 /\ o <> 0) /\
  (ii <> dxj cx -> o = 0 \/ f <> re_fd e1)).
{ intros ii Hii. destruct (Nat.eq_dec ii (dxj cx)) as [->|Hne].
  - pose proof Hsrc as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    unfold dHA, ASRC in V1, V2.
    exists (hs_fd h1), (hs_open h1).
    split; [exact V1|]. split; [exact V2|]. split; [lia|]. split; [rewrite Hopen; lia|].
    split; [intros _; split; [exact Hfd | rewrite Hopen; lia]|]. intros Hcc; contradiction.
  - assert (HfdvX : 0 <= re_fd (dxe cx) < 2 ^ 31) by (rewrite <- Sfd; exact Hfdv).
    destruct (dt_others_canon W1 m1 (dxj cx) (re_fd (dxe cx)) ii Hoth Hii Hne HfdvX)
      as (f & o & V1 & V2 & Bf & Bo & Hdis).
    unfold ASRC in V1, V2.
    exists f, o. split; [exact V1|]. split; [exact V2|]. split; [exact Bf|]. split; [exact Bo|].
    split; [intros Hcc; contradiction|]. intros _. rewrite Sfd.
    destruct Hdis as [Hq|Hq]; [left; exact Hq|right].
    rewrite (Z.mod_small f (2 ^ 32)) in Hq by lia.
    rewrite (Z.mod_small (re_fd (dxe cx)) (2 ^ 32)) in Hq by lia. exact Hq. }
destruct (Hslot 0%nat ltac:(lia)) as (f0 & o0 & V00 & V01 & B00 & B01 & Hjj0 & Hoo0).
destruct (Hslot 1%nat ltac:(lia)) as (f1 & o1 & V10 & V11 & B10 & B11 & Hjj1 & Hoo1).
destruct (Hslot 2%nat ltac:(lia)) as (f2 & o2 & V20 & V21 & B20 & B21 & Hjj2 & Hoo2).
destruct (Hslot 3%nat ltac:(lia)) as (f3 & o3 & V30 & V31 & B30 & B31 & Hjj3 & Hoo3).
replace (rg_s RG + 96 * Z.of_nat 0) with (rg_s RG) in V00 by lia.
replace (rg_s RG + 96 * Z.of_nat 0 + 4) with (rg_s RG + 4) in V01 by lia.
replace (rg_s RG + 96 * Z.of_nat 1) with (rg_s RG + 96) in V10 by lia.
replace (rg_s RG + 96 * Z.of_nat 1 + 4) with (rg_s RG + 100) in V11 by lia.
replace (rg_s RG + 96 * Z.of_nat 2) with (rg_s RG + 192) in V20 by lia.
replace (rg_s RG + 96 * Z.of_nat 2 + 4) with (rg_s RG + 196) in V21 by lia.
replace (rg_s RG + 96 * Z.of_nat 3) with (rg_s RG + 288) in V30 by lia.
replace (rg_s RG + 96 * Z.of_nat 3 + 4) with (rg_s RG + 292) in V31 by lia.
remember (Eimg (Ereg regs1 (dt_dsc_extra f0 o0 f1 o1 f2 o2 f3 o3))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E8 : ew E 8 = Z_to_bv 64 ((rg_s RG + 4) / 8))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 ((rg_s RG + 0) / 8))
  by (rewrite (EREG 9%nat 9%bv) by (first [lia | reflexivity]); rewrite Z.add_0_r; exact R9).
assert (E14 : ew E 14 = Z_to_bv 64 (re_fd e1))
  by (rewrite (EREG 14%nat 14%bv) by (first [lia | reflexivity]); exact R14).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E24 : ew E 24 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat i))
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (E32 : ew E 32 = Z_to_bv 64 f0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 o0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 f1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 o1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 o2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 f3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 o3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (SHOK : sh_ok SEGS BxT SHdsc E (mrestrict (w_H W1) m1)).
{ unfold SHdsc, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_azs ly1 S1 W1 m1 md1 E 18 (rg_s RG) 384 HAR);
    [ change 384 with (4 * ASRC); exact HGSZ
    | exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia))
    | exact (U_atom E 18 (rg_s RG) E18 ltac:(lia)) | lia | lia | lia ]. }
assert (HS : st_ok_pi SEGS VAL E (ss_dsc i)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_scan)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_dsc. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                       | intros X; discriminate X |].
    + cbn [sv_denot]. exact R12.
    + cbn [sv_denot]. exact R19.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, dt_dsc_gs.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 32 0) f0);
        [exact (den_atom0 E 32 f0 E32 ltac:(lia)) | zside | zside | rewrite Z.add_0_r; exact V00].
    + apply (chunk_ok_val SEGS E _ _ 4 4 (SOff 33 0) o0);
        [exact (den_atom0 E 33 o0 E33 ltac:(lia)) | zside | zside | exact V01].
    + apply (chunk_ok_val SEGS E _ _ 96 4 (SOff 34 0) f1);
        [exact (den_atom0 E 34 f1 E34 ltac:(lia)) | zside | zside | exact V10].
    + apply (chunk_ok_val SEGS E _ _ 100 4 (SOff 35 0) o1);
        [exact (den_atom0 E 35 o1 E35 ltac:(lia)) | zside | zside | exact V11].
    + apply (chunk_ok_val SEGS E _ _ 192 4 (SOff 36 0) f2);
        [exact (den_atom0 E 36 f2 E36 ltac:(lia)) | zside | zside | exact V20].
    + apply (chunk_ok_val SEGS E _ _ 196 4 (SOff 37 0) o2);
        [exact (den_atom0 E 37 o2 E37 ltac:(lia)) | zside | zside | exact V21].
    + apply (chunk_ok_val SEGS E _ _ 288 4 (SOff 38 0) f3);
        [exact (den_atom0 E 38 f3 E38 ltac:(lia)) | zside | zside | exact V30].
    + apply (chunk_ok_val SEGS E _ _ 292 4 (SOff 39 0) o3);
        [exact (den_atom0 E 39 o3 E39 ltac:(lia)) | zside | zside | exact V31].
  - cbn [pairwise_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [dt_dsc_facts f_atoms atoms_ok]. unfold afact_ok, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite U18, U21. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert HGS1 HGS2 HGS8. clear. unfold SB, SHADOW_OFF. intros.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
destruct i as [|[|[|[|i]]]]; [| | | | lia].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 0 + 4)) HS
    (eq_trans Ra1 (dt_den_add_sh E 8 (rg_s RG) 4 (Z.of_nat 0) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite (dt_beqz_sx E 33 o0 E33 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (_ & Ho); lia).
    paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite !wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
    dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
    dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
    dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
    dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
    split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
    split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
    split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
    split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
    split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
    split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
    split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
    split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
    split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split.
    { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      f_equal; cbn [Z.of_nat]; lia. }
    split; [lia|].
    split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 0 + 0)) HS
      (eq_trans Ra1 (dt_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 0) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (dt_beq_sx E 32 14 f0 (re_fd e1) E32 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (dt_beqz_sx E 33 o0 E33 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (0 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 0 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo0 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)), R18.
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (dt_beq_sx E 32 14 f0 (re_fd e1) E32 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (Hf & _); contradiction).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
      dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
      dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split.
      { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        f_equal; cbn [Z.of_nat]; lia. }
      split; [lia|].
      split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 1 + 4)) HS
    (eq_trans Ra1 (dt_den_add_sh E 8 (rg_s RG) 4 (Z.of_nat 1) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite (dt_beqz_sx E 35 o1 E35 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (_ & Ho); lia).
    paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite !wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
    dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
    dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
    dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
    dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
    split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
    split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
    split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
    split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
    split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
    split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
    split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
    split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
    split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split.
    { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      f_equal; cbn [Z.of_nat]; lia. }
    split; [lia|].
    split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 1 + 0)) HS
      (eq_trans Ra1 (dt_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 1) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (dt_beq_sx E 34 14 f1 (re_fd e1) E34 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (dt_beqz_sx E 35 o1 E35 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (1 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 1 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo1 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (den_atom E 18 (rg_s RG) 96 E18 ltac:(lia) ltac:(lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (dt_beq_sx E 34 14 f1 (re_fd e1) E34 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (Hf & _); contradiction).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
      dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
      dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split.
      { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        f_equal; cbn [Z.of_nat]; lia. }
      split; [lia|].
      split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 2 + 4)) HS
    (eq_trans Ra1 (dt_den_add_sh E 8 (rg_s RG) 4 (Z.of_nat 2) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite (dt_beqz_sx E 37 o2 E37 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (_ & Ho); lia).
    paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite !wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
    dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
    dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
    dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
    dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
    split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
    split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
    split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
    split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
    split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
    split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
    split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
    split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
    split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split.
    { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      f_equal; cbn [Z.of_nat]; lia. }
    split; [lia|].
    split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 2 + 0)) HS
      (eq_trans Ra1 (dt_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 2) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (dt_beq_sx E 36 14 f2 (re_fd e1) E36 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (dt_beqz_sx E 37 o2 E37 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (2 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 2 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo2 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (den_atom E 18 (rg_s RG) 192 E18 ltac:(lia) ltac:(lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (dt_beq_sx E 36 14 f2 (re_fd e1) E36 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (Hf & _); contradiction).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
      dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
      dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split.
      { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        f_equal; cbn [Z.of_nat]; lia. }
      split; [lia|].
      split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 3 + 4)) HS
    (eq_trans Ra1 (dt_den_add_sh E 8 (rg_s RG) 4 (Z.of_nat 3) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite (dt_beqz_sx E 39 o3 E39 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (_ & Ho); lia).
    exfalso. lia.
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 3 + 0)) HS
      (eq_trans Ra1 (dt_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 3) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (dt_beq_sx E 38 14 f3 (re_fd e1) E38 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (dt_beqz_sx E 39 o3 E39 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (3 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 3 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo3 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (den_atom E 18 (rg_s RG) 288 E18 ltac:(lia) ltac:(lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (dt_beq_sx E 38 14 f3 (re_fd e1) E38 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (Hf & _); contradiction).
      exfalso. lia.

Qed.

(* ---- The scan loop: at most four bodies, because the harness's own slot j is below four. ---- *)
Lemma dt_DSC_le : forall cx sg D i W1 c1, DSC cx sg D i W1 c1 -> (i <= dxj cx)%nat.
Proof.
intros cx sg D i W1 c1 (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hij & _).
exact Hij.
Qed.

Lemma dt_scan_loop : forall n cx sg D i W1 c1,
(4 - i <= n)%nat -> DBASE B MT MMAX RG cx -> DSC cx sg D i W1 c1 ->
(forall W2 c2, DT2 B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
induction n as [|n IH]; intros cx sg D i W1 c1 Hn HB HDSC Kf.
- exfalso. pose proof (dt_DSC_le cx sg D i W1 c1 HDSC) as Hij.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _). lia.
- apply (dt_scan_step cx sg D i W1 c1 HB HDSC); [|exact Kf].
  intros W2 c2 H2. exact (IH cx sg D (S i) W2 c2 ltac:(lia) HB H2 Kf).
Qed.

(* ---- The walk from DT1 (0x8326c) to the loop's head (0x832b4): four shadow checks of the relay entry,
   s->used / s->buf / s->cap / s->fd, the memcpy destination and the room, and the shadow base into s8. ---- *)
Lemma dt_den_add2 : forall E (n m : nat) v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w ->
0 <= v -> 0 <= w -> v + w < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = w64 (v + w).
Proof.
intros E n m v w Hn Hm Hv Hw Hvw. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn) by lia. rewrite (U_atom E m w Hm) by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma dt_den_sx : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = w64 v.
Proof.
intros E n v Hn Hv. apply bv_eq. rewrite U_sext32'.
assert (HU : bv_unsigned (sv_denot E (SOff n 0)) = v) by exact (U_atom E n v Hn ltac:(lia)).
rewrite HU, (sx32_small v) by lia. unfold w64. symmetry. apply unsigned_lit_small. lia.
Qed.
Lemma dt_den_room : forall E cap used,
ew E 33 = Z_to_bv 64 cap -> ew E 34 = Z_to_bv 64 used -> 0 <= used <= cap -> cap <= 16384 ->
sv_denot E (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))) = w64 (cap - used).
Proof.
intros E cap used H33 H34 Hu Hc. rewrite denot_lit_U. unfold w64. f_equal.
apply (dt_U_room E cap used); [rewrite H33; apply unsigned_lit_small; lia
                              |rewrite H34; apply unsigned_lit_small; lia | lia | lia].
Qed.

Lemma dt_scan : forall cx sg D W1 c1,
DBASE B MT MMAX RG cx -> DT1 cx sg D W1 c1 ->
(forall W2 c2, DT2 B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx sg D W1 c1 HB HDT1 Kf.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDT1 as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & R19 & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 &
  F224 & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & Hgarr0 & Hawr0 & HEOK0 & Hj4 & Hsrc0 & Hoth0 & HfdB &
  HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16848) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16848 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
pose proof HSAME as (Sfd & Seof & Shfd & Shopen & HSrest).
assert (Hfd : hs_fd h1 = re_fd e1) by (rewrite Shfd, HfdB; exact (eq_sym Sfd)).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (Hfdv : 0 <= re_fd e1 < 2 ^ 31) by (pose proof HEOK as (_ & _ & _ & _ & Hq & _); exact Hq).
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & Hq & _); exact Hq).
(* the relay's table is off the image, so the entry and g_s do not overlap *)
assert (Hoff : dxG cx + 896 <= 0x10000 \/ 0x5fb000 <= dxG cx).
{ pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as Hq.
  unfold off_img in Hq. rewrite RQT in Hq. exact Hq. }
assert (Hcapb : 0 <= re_cap e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hl & Hq & _); lia).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hbufb : 0 <= re_buf e1 /\ re_buf e1 + re_cap e1 <= alloc_ceiling).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _).
  destruct Hq as [(Hc & Hb & Hu)|(Hc & Hin & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hin) as (_ & H4 & Hcl & _).
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq). lia. }
(* the four slots of g_s, as the scan reads them *)
assert (Hslot : forall ii, (ii < 4)%nat -> exists f o,
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii) 4 f /\
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii + 4) 4 o /\
  0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32).
{ intros ii Hii. destruct (Nat.eq_dec ii (dxj cx)) as [->|Hne].
  - pose proof Hsrc as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    unfold dHA, ASRC in V1, V2.
    exists (hs_fd h1), (hs_open h1).
    split; [exact V1|]. split; [exact V2|]. split; [lia|]. rewrite Hopen; lia.
  - assert (HfdvX : 0 <= re_fd (dxe cx) < 2 ^ 31) by (rewrite <- Sfd; exact Hfdv).
    destruct (dt_others_canon W1 m1 (dxj cx) (re_fd (dxe cx)) ii Hoth Hii Hne HfdvX)
      as (f & o & V1 & V2 & Bf & Bo & _).
    unfold ASRC in V1, V2. exists f, o. split; [exact V1|]. split; [exact V2|]. split; [exact Bf | exact Bo]. }
destruct (Hslot 0%nat ltac:(lia)) as (f0 & o0 & V00 & V01 & B00 & B01).
destruct (Hslot 1%nat ltac:(lia)) as (f1 & o1 & V10 & V11 & B10 & B11).
destruct (Hslot 2%nat ltac:(lia)) as (f2 & o2 & V20 & V21 & B20 & B21).
destruct (Hslot 3%nat ltac:(lia)) as (f3 & o3 & V30 & V31 & B30 & B31).
replace (rg_s RG + 96 * Z.of_nat 0) with (rg_s RG) in V00 by lia.
replace (rg_s RG + 96 * Z.of_nat 0 + 4) with (rg_s RG + 4) in V01 by lia.
replace (rg_s RG + 96 * Z.of_nat 1) with (rg_s RG + 96) in V10 by lia.
replace (rg_s RG + 96 * Z.of_nat 1 + 4) with (rg_s RG + 100) in V11 by lia.
replace (rg_s RG + 96 * Z.of_nat 2) with (rg_s RG + 192) in V20 by lia.
replace (rg_s RG + 96 * Z.of_nat 2 + 4) with (rg_s RG + 196) in V21 by lia.
replace (rg_s RG + 96 * Z.of_nat 3) with (rg_s RG + 288) in V30 by lia.
replace (rg_s RG + 96 * Z.of_nat 3 + 4) with (rg_s RG + 292) in V31 by lia.
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_sc_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1) (re_fd e1)
  f0 o0 f1 o1 f2 o2 f3 o3))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (re_fd e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 f0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 o0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 f1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 o1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 f2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 o2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 10)).
assert (E43 : ew E 43 = Z_to_bv 64 f3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 11)).
assert (E44 : ew E 44 = Z_to_bv 64 o3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 12)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs1 25 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs1 26 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs1 23 = sv_denot E (dt_sh 32 32))
  by (rewrite (dt_den_sh E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs1 24 = sv_denot E (dt_sh 32 0))
  by (rewrite (dt_den_sh E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite (dt_den_gv E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs1 8 = sv_denot E (dt_gv 4))
  by (rewrite (dt_den_gv E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_sc
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_mid)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sc. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R19].
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold region_ok, dt_sc_frame, dt_sc_sa, dt_sc_gs, dt_gs_chunks;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact (dt_den_sh E 32 (dxSA cx) 16 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact (dt_den_sh E 32 (dxSA cx) 24 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F224 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 36 0) (re_fd e1));
          [exact (den_atom0 E 36 (re_fd e1) E36 ltac:(lia)) | zside | zside | ].
        rewrite Z.add_0_r. exact (dt_entry_fd W1 m1 (dxSA cx) e1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 35 0) (re_buf e1));
          [exact (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_buf W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_cap W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
    + cbn [base_val]. rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 37 0) f0);
          [exact (den_atom0 E 37 f0 E37 ltac:(lia)) | zside | zside | rewrite Z.add_0_r; exact V00].
      * apply (chunk_ok_val SEGS E _ _ 4 4 (SOff 38 0) o0);
          [exact (den_atom0 E 38 o0 E38 ltac:(lia)) | zside | zside | exact V01].
      * apply (chunk_ok_val SEGS E _ _ 96 4 (SOff 39 0) f1);
          [exact (den_atom0 E 39 f1 E39 ltac:(lia)) | zside | zside | exact V10].
      * apply (chunk_ok_val SEGS E _ _ 100 4 (SOff 40 0) o1);
          [exact (den_atom0 E 40 o1 E40 ltac:(lia)) | zside | zside | exact V11].
      * apply (chunk_ok_val SEGS E _ _ 192 4 (SOff 41 0) f2);
          [exact (den_atom0 E 41 f2 E41 ltac:(lia)) | zside | zside | exact V20].
      * apply (chunk_ok_val SEGS E _ _ 196 4 (SOff 42 0) o2);
          [exact (den_atom0 E 42 o2 E42 ltac:(lia)) | zside | zside | exact V21].
      * apply (chunk_ok_val SEGS E _ _ 288 4 (SOff 43 0) f3);
          [exact (den_atom0 E 43 f3 E43 ltac:(lia)) | zside | zside | exact V30].
      * apply (chunk_ok_val SEGS E _ _ 292 4 (SOff 44 0) o3);
          [exact (den_atom0 E 44 o3 E44 ltac:(lia)) | zside | zside | exact V31].
  - apply pairwise_disjoint_of_extents.
    unfold dt_sc_frame, dt_sc_sa, dt_sc_gs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1 HGS1 HGS2 Hoff HGle HSAhi. clear.
    unfold DRAIN_FRAME, AENT, ATABLE. intros.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_sc_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHsc E (mrestrict (w_H W1) m1)).
{ unfold SHsc, sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (dt_shent_sub ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
    + exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
    + exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
    + lia.
    + lia.
    + rewrite RQT. unfold AENT, ATABLE in HSAhi. lia.
  - apply (dt_shent_azs ly1 S1 W1 m1 md1 E 18 (rg_s RG) 384 HAR);
      [ change 384 with (4 * ASRC); exact HGSZ
      | exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia))
      | exact (U_atom E 18 (rg_s RG) E18 ltac:(lia)) | lia | lia | lia ]. }
paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
rewrite ?wvb_collapse in HJ.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m1 a)
  by (intros a; exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _)))).
assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ _ HG0 Ha)).
dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
pmkst HS.
apply (dt_scan_loop 4 cx sg D 0 _ _ ltac:(lia) HB); [|exact Kf].
unfold DSC.
eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
split; [reflexivity|].
split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
split; [rewrite X25; exact (eq_trans (eq_sym R25') R25)|].
split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
split; [rewrite X26; exact (eq_trans (eq_sym R26') R26)|].
split; [rewrite X18, (dt_den_reg E 18 _ E18); reflexivity|].
split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
split; [rewrite X8; exact (eq_trans (eq_sym R8') R8)|].
split; [rewrite X21, (dt_den_reg E 21 _ E21); reflexivity|].
split; [rewrite X10, (dt_den_add2 E 34 35 (re_used e1) (re_buf e1) E34 E35
  ltac:(lia) ltac:(lia) ltac:(lia)); unfold w64; f_equal; lia|].
split; [rewrite X13; exact (dt_den_room E (re_cap e1) (re_used e1) E33 E34 ltac:(lia) ltac:(lia))|].
split; [rewrite X14; exact (dt_den_sx E 36 (re_fd e1) E36 ltac:(lia))|].
split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
split; [rewrite X19; cbn [sv_denot]; reflexivity|].
split; [rewrite X24, (dt_den_reg E 21 _ E21); unfold w64; f_equal; cbn [Z.of_nat]; lia|].
split; [lia|].
split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms) md1 _ k1 k1 e1 h1 sg out1 ev1
  (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
split; [exact Hlater | exact Hbud].
Qed.

(* The TOP TAIL (DT2 0x83314 -> the EINTR round / the empty-pending test / the data round) is the frozen statement
   dr_toptail_stmt (W_drain_topb_cx.v), proved in its own file; dr_top takes it as a premise, so nothing here is
   Admitted (W7Drain-2 at the merge of this branch; it was an Admitted placeholder lemma). *)
Hypothesis dt_tail : dr_toptail_stmt B MT MMAX RG.

(* ---- The segment: the growth test, then the scan and the three exits. ---- *)
Theorem dr_top : @dr_top_stmt fx rc SK PI B MT MMAX RG.
Proof.
intros cx s1 D W1 c1 HB HDI Kdi Kend Krb.
assert (KT2 : forall W2 c2, DT2 B MT MMAX RG cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx))
  by (intros W2 c2 H; exact (dt_tail cx (dgrow s1) D W2 c2 HB H Kdi Kend Krb)).
assert (KT1 : forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx))
  by (intros W2 c2 H; exact (dt_scan cx (dgrow s1) D W2 c2 HB H KT2)).
destruct (Z.le_gt_cases 4096 (drain_b_c.ds_cap s1 - ulen s1)) as [Hge|Hlt].
- exact (dt_nogrow cx s1 D W1 c1 HB HDI Hge KT1).
- exact (dt_grow cx s1 D W1 c1 HB HDI Hlt KT1).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice A, 2026-10-30): dr_top_x proves W_drain_cx_x.v's dr_top_stmt_x from
   W_drain_topb_cx.v's dr_toptail_stmt_x (Section hypothesis dt_tail_x; W_drain_topb.v dr_toptail_x proves it), over
   W_drain_cx_x.v's Section variables, with HP0 (every ghost list empty, so every cut of the walk is read at Hp = [])
   and realloc #1 through the caller-context rule at its context fact HCTX_re1.
   THE ROOM ROUND at realloc #1 (0x83248, returns to 0x8324c): the request costs MT_rk's 2 (dt_grow_rk); the rule
   runs at kr' := MT_rk's charge of the tail plus the entry's kr (dt_grow_room_rk), its count premise from the cut's
   counts; DT1_x takes its room from the rule's post and its counts by dt_grow_cnt (the new block in place of the
   old one, within the request's peak).  The relay table / g_s disjointness is YCbqG.blk_img_x with HG.
   Everything above is unchanged.  The AR-free names of Section c above are CITED with the Section variables they
   abstracted; the lemmas whose statements or proofs name AR, the journal, DMEM, the cuts or the run chain have
   their _x twin here (same name with _x when the AR name exists). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_laws_x W_img_x W_tr_cnt ReplyCnt.
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
(* the instance's laws, and no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
(* a ROM byte survives a callee's journal (W_journal_x.v rom_out / ajournal_gx_rom_view_x): it is not a walk global,
   errno or the sink's overflow head, and if it is an allocator static it is pinned as a const cell.  The instance
   discharges it at the pinned placement by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
(* aout_at's three read-only cells are program globals off the allocator's statics, so an allocator or program
   call keeps them (found by GsFree at free #2: they are not in G_DR; send_line's W_send_line_cx.v HGO) *)
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
(* the allocator's site rules in their caller-context forms at RP (W_journal_x.v Section hc), one context table per
   allocator entry; every drain site hands the rule a cut chain, so its trace is its return address alone *)
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x170] CTX_R.   (* realloc #1 returns to 0x8324c *)
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
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
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* the walk at the empty ghost list (HP0): every cut's ARx state, journal and memory core at Hp = [] *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation DMEM0 cx ly S W m md k e h s out ev sent LB :=
  (DMEM_x B PST ARx RG cx [] ly S [] W m md k e h s out ev sent LB).
Local Notation dbud0 cx := (dbud_x B MT RP MMAX cx).
Local Notation AJ0 cx ly S W m md k :=
  (@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
     (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx) (dxmd cx) [] ly S [] W m md k).
(* a cut's ghost list Hp1 is [] (HP0 at the cut's state, which its memory core's journal ends in) *)
Ltac dt_hp1 H Hp1 := let E := fresh "EHp" in
  assert (E : Hp1 = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact (proj1 H)); subst Hp1.
(* the run tactics over the generic journal (W_kit_x.v): every run of the walk is paj_run_x_x / paj_run_to_x_x *)
Local Ltac paj_run_tok RUN HS HJ SHOK Bspan := paj_run_tok_x RUN HS HJ SHOK Bspan.
Local Ltac paj_run_to_tok RUNTO HS HJ SHOK Bspan stop := paj_run_to_tok_x RUNTO HS HJ SHOK Bspan stop.
(* membership in the walk's globals G_DR *)
Ltac dt_ing_tac := unfold G_DR; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
Ltac dt_len := rewrite ?length_app, ?dt_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes;
  cbn [length].

(* ---- The walk's symbolic values: a shadow address and a pre-shifted g_s field address. ---- *)
#[local] Notation dt_sh m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0)).
#[local] Notation dt_gv c := (SAlu ALU_SRL (SOff 18 c) (SLit 3)).
#[local] Notation BxT := (SOff 21 0).
(* a register read off a symbolic state, with its value left as the state's own expression *)
Ltac dt_reg HS r Hr :=
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

(* ---- A zero-shadow range inside a live block, as the walk's shadow-entry obligation. ---- *)
Lemma dt_shent_sub_x : forall ly S (W : world SEGS) mem md E (m : nat) p n q lo hi,
AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E m p n q lo hi HAR Hin HB Hm H1 H2 H3.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
rewrite <- (aview_rd_of SEGS).
destruct (alx_shadow _ _ _ LAWS ly S [] W mem md p n HAR Hin (fun h (Hh : In h []) => match Hh with end))
  as [Hbs _].
split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
  eapply block_shadow_range; [exact Hbs | lia | lia].
- destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
  intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Definition DT1_x (cx : dcx) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_mid) regs1 m1 md1 /\
dregs_top RG cx regs1 /\ getr regs1 19 = w64 384 /\
DMEM0 cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud0 cx kr ly1 S1 spent tl.

(* No live block is listed twice: two copies would have to be disjoint from themselves. *)
Lemma dt_no_dup_block_x : forall ly S Hp (W : world SEGS) mem md x l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: x :: l) -> 0 <= snd x -> False.
Proof.
intros ly S Hp W mem md x l HAR HP Hn.
pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W mem md x x l HAR HP) as Hd.
pose proof (req_size_pos (snd x) Hn) as (Hr & _).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* The buffer the round hands to realloc: if it was already a block when drain was entered, it is one of the
   blocks the walk declared.  It cannot be the relay's table (its requested size is not a capacity), and it
   cannot be one of the blocks drain found live and left alone (dxrest): the entry's buffer is a block at the
   cut too, so the cut's block list would hold it twice. *)
Lemma dt_buf_fp_x : forall cx ly1 S1 Hp1 (W1 : world SEGS) m1 md1 bl p n,
ARx ly1 S1 Hp1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: bl ++ dxrest cx) -> In (p, n) bl ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++
     dxrest cx) ->
In (p, n) (ablocks B (dxly cx) (dxS cx)) -> 0 <= n -> n <> ATABLE ->
forall i, 0 <= i < req_size n -> inFP (dFP cx) (p + i).
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 bl p n HAR HPc Hbl HP0' Hin0 Hn Hnt i Hi.
unfold dFP, dr_fp.
assert (Hin : In (p, n) ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
  aout_blks (dxcap cx) (dxout cx) ++ dxrest cx)) by (eapply Permutation_in; [exact HP0' | exact Hin0]).
destruct Hin as [Heq | Hin]; [injection Heq as _ Heq; congruence|].
apply in_app_or in Hin as [Hin | Hin]; [exact ((dt_inFP_of_blocks RG) _ p n i _ (in_or_app _ _ _ (or_introl Hin)) Hi)|].
apply in_app_or in Hin as [Hin | Hin];
  [exact ((dt_inFP_of_blocks RG) _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hin)))) Hi)|].
apply in_app_or in Hin as [Hin | Hrest];
  [exact ((dt_inFP_of_blocks RG) _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hin)))) Hi)|].
exfalso.
destruct (in_split _ _ Hbl) as (b1 & b2 & Eb).
destruct (in_split _ _ Hrest) as (d1 & d2 & Ed).
apply (dt_no_dup_block_x ly1 S1 Hp1 W1 m1 md1 (p, n) ((dxG cx, ATABLE) :: b1 ++ b2 ++ d1 ++ d2)); [exact HAR | | exact Hn].
eapply Permutation_trans; [exact HPc|].
rewrite Eb, Ed, <- !app_assoc.
apply Permutation_sym.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: b1) (l2 := b2 ++ d1 ++ (p, n) :: d2).
cbn [app]. rewrite !app_assoc.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: (b1 ++ b2) ++ d1) (l2 := d2).
apply Permutation_refl.
Qed.

Ltac dt_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

(* two blocks at distinct places of a permutation of the live blocks are apart *)
Lemma dt_sep_head_x : forall ly S Hp (W : world SEGS) m md x L y,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

(* ---- The room round at realloc #1 (W_drain_cx_x.v dbud_x): the request's room and its counts. ----
   MT_rk charges every request of a trace (a malloc and a realloc alike: mo_malloc + mo_free = 2, a free 1), so
   the growth's one request costs 2 and what the rest of the walk owes is the tail's charge; the counts move by
   the request's own net count (the new block in place of the old one), which the peak of the trace it opens
   covers (ReplyCnt.tr_peakP, the new block counted before the old one goes). *)
Lemma dt_tr_cost_app_g : forall (M : ameter_ops) (t1 t2 : dtrace),
tr_cost M (t1 ++ t2) = tr_cost M t1 + tr_cost M t2.
Proof.
intros M t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma dt_tr_cost_rk_nonneg : forall (t : dtrace), 0 <= tr_cost MT_rk t.
Proof.
intros t. induction t as [|ev t IH]; [exact (Z.le_refl 0)|].
change (ev :: t) with ([ev] ++ t). rewrite dt_tr_cost_app_g.
assert (Hev : 0 <= tr_cost MT_rk [ev]) by (destruct ev; vm_compute; discriminate).
lia.
Qed.
Lemma dt_grow_rk : forall cap used j b, cap - used < 4096 ->
tr_cost MT_rk (fst (drain_b_c.grow_tr cap used j b)) = 2.
Proof.
intros cap used j b Hlt. unfold drain_b_c.grow_tr. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt).
cbn [fst]. destruct (cap =? 0); reflexivity.
Qed.
(* the room the request needs, out of the cut's: 2 for the request, the tail's charge on top of kr after it *)
Lemma dt_grow_room_rk : forall S cap used j b (t : dtrace) (kr : nat), cap - used < 4096 ->
rp_RM RP S (Z.to_nat (tr_cost MT_rk (fst (drain_b_c.grow_tr cap used j b) ++ t)) + kr) ->
rp_RM RP S (2 + (Z.to_nat (tr_cost MT_rk t) + kr)).
Proof.
intros S cap used j b t kr Hlt H.
rewrite dt_tr_cost_app_g, (dt_grow_rk cap used j b Hlt) in H.
pose proof (dt_tr_cost_rk_nonneg t) as Ht.
replace (2 + (Z.to_nat (tr_cost MT_rk t) + kr))%nat with (Z.to_nat (2 + tr_cost MT_rk t) + kr)%nat by lia.
exact H.
Qed.
(* the counts after the request: at most the cut's, with the request's peak spent *)
Lemma dt_grow_cnt : forall ly1 S1 ly2 S2 buf cap nc res used j b (t : dtrace) P,
cap - used < 4096 -> nc = (if cap =? 0 then 8192 else cap * 2) ->
(cap = 0 -> buf = 0) -> (cap <> 0 -> buf <> 0) ->
(buf = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(buf <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (buf, cap) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) + ReplyCnt.tr_peakP P t <=
Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) + ReplyCnt.tr_peakP P (fst (drain_b_c.grow_tr cap used j b) ++ t).
Proof.
intros ly1 S1 ly2 S2 buf cap nc res used j b t P Hlt Enc Hz Hnz HA HB'.
unfold drain_b_c.grow_tr. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt). cbn [fst app].
pose proof (ReplyCnt.tr_peakP_nonneg _ P t) as Ht.
destruct (Z.eqb_spec cap 0) as [E|E]; cbn [ReplyCnt.tr_peakP]; subst nc.
- rewrite (ReplyCnt.acnt_perm P _ _ (HA (Hz E))), acnt_cons. cbn [snd]. unfold ReplyCnt.zb.
  destruct (P 8192); lia.
- destruct (HB' (Hnz E)) as (l1 & l2 & E1 & P2).
  rewrite (ReplyCnt.acnt_perm P _ _ P2), acnt_cons, E1, !ReplyCnt.acnt_app, acnt_cons. cbn [snd].
  unfold ReplyCnt.zb. destruct (P (cap * 2)), (P cap); lia.
Qed.

(* The loop head 0x832b4 after the first i slots were passed over: a2 = 96 i, s8 = the shadow base + 12 i,
   s3 = 0x180, a0 = s->buf + s->used, a3 = s->cap - s->used and a4 = s->fd.  The scan has not yet reached
   the harness's own slot j (i <= j), so every slot passed over was closed or on another fd. *)
Definition DSC_x (cx : dcx) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (i : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_scan) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 27 = w64 (dxSA cx + 24) /\ getr regs1 26 = w64 (dxSA cx + 16) /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
getr regs1 14 = w64 (re_fd e1) /\ getr regs1 12 = w64 (96 * Z.of_nat i) /\
getr regs1 19 = w64 384 /\ getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat i) /\
(i <= dxj cx)%nat /\
DMEM0 cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud0 cx kr ly1 S1 spent tl.

(* the 4 * 96 bytes of g_s as the walk's shadow-entry obligation (HGSZ) *)
Lemma dt_shent_azs_x : forall ly S (W : world SEGS) mem md E (m : nat) q n,
AR0 ly S W mem md -> azs B q n -> U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
0 <= n -> 0x10000 <= q -> q + n <= 0x5fb000 ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m 0 n).
Proof.
intros ly S W mem md E m q n HAR Hz HB Hm Hn Hq1 Hq2.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
split.
- rewrite Z.add_0_r, Z.sub_0_r. exact (azs_range_addressable_x B ARx LAWS ly S [] W mem md q n HAR Hz).
- intros a Ha. unfold SHADOW_OFF. lia.
Qed.

(* ---- Route R: the R twins of this Section's walk lemmas, at a world relation R that contains wle (the journal
   ajournal_gx_xR and the step relation YA0nH.SRrG at R).  Each <name>R is <name> with the journal, the cuts
   DMEM_x / DI_x / DT1_x / DSC_x / DT2_x, dPOST_x and SRr replaced by their R twins; the lemmas that state neither
   are used as they are.  After this Section every strict lemma the walk uses is its twin at R := wle.  Realloc #1
   goes through AREALLOC_R, the caller-context rule at R (W_journal_x.v arealloc_cf_rule_c_xR), with its RO premise
   from the call memory's ARx (RO_ARx) and its HA premise from the call's meter fact (HA_call). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp W mem md, ARx ly S Hp W mem md -> RO mem.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PI).
Local Notation DMEM0R cx ly S W m md k e h s out ev sent LB :=
  (DMEM_xR B PST ARx RG R cx [] ly S [] W m md k e h s out ev sent LB).
Local Notation AJ0R cx ly S W m md k :=
  (@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
     (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx) (dxmd cx) [] ly S [] W m md k).
Ltac dt_hp1R H Hp1 := let E := fresh "EHp" in
  assert (E : Hp1 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact (proj1 H)); subst Hp1.
Lemma dt_DMEM_kept_xR : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
AJ0R cx ly1 S1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM0R cx ly1 S1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
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
split; [exact (dt_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => KL x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact ((dt_aentry_okx_kept B RG) ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  ((dt_aentry_blks_in B RG HGSB) ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  ((dt_asrc_blks_in B RG HGSB) ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact ((dt_aout_blks_in B RG HGSB) ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.
Definition DT1_xR (cx : dcx) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_mid) regs1 m1 md1 /\
dregs_top RG cx regs1 /\ getr regs1 19 = w64 384 /\
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud0 cx kr ly1 S1 spent tl.

Lemma dt_nogrow_xR : forall cx kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DI_xR B PST ARx MT RP MMAX RG R cx [] kr s1 D W1 c1 ->
4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
(forall W2 c2, DT1_xR cx kr (dgrow s1) D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr s1 D W1 c1 HB HDI Hge K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDI as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
dt_hp1R HMEM Hp1.
pose proof Hregs as (Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof HEOK as (Heof & Hskipv & Hpad1 & Hpad2 & Hfdv & Hcapv & HUlen & Hucap & Hbufc & Hnheld & Hheldc &
  HND1 & HND2 & Hkeys).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= 16384) by lia.
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_ng_extra (dxSA cx) (re_cap e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs1 25 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs1 26 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs1 23 = sv_denot E (dt_sh 32 32))
  by (rewrite ((dt_den_sh RG) E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs1 24 = sv_denot E (dt_sh 32 0))
  by (rewrite ((dt_den_sh RG) E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs1 8 = sv_denot E (dt_gv 4))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_ng
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ng. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_ng_frame, dt_ng_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
        [ exact ((dt_den_sh RG) E 32 (dxSA cx) 24 E32 E21 ltac:(lia) ltac:(lia))
        | unfold shadow_addr, SHADOW_OFF;
          (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                  | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia); zside])
        | zside
        | exact F224 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [ exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_used RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [ exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_cap RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_ng_frame, dt_ng_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_ng_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF.
    cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub_x ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUNR BRR HS SHOK DBspan.
- (* 4096 <= cap - used: the round needs no growth, straight on to 0x8326c *)
  paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_mid.
  { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  rewrite wvb_collapse in HJ.
  (* the two runs store nothing: every region of ss_ng is read-only, so no byte of the walk's memory moves *)
  assert (Hnw : forall x, ~ in_wrange E (ss_mem ss_ng) x).
  { intros x (r & Hin & Hr). cbv [ss_mem ss_ng dt_ng_frame dt_ng_sa] in Hin.
    destruct Hin as [Hq|[Hq|[]]]; subst r;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a.
    rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (Hnw _))).
    exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (Hnw _))). }
  assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ _ HG1 (apresent_grows _ _ _ _ HG0 Ha))).
  dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
  dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (18%bv : bv 5) X18.
  dt_reg HS (21%bv : bv 5) X21. dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23.
  dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26.
  dt_reg HS (27%bv : bv 5) X27.
  pmkst HS.
  apply K. rewrite (dgrow_id s1 Hge). unfold DT1_xR.
  eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
    split; [rewrite X25; exact (eq_trans (eq_sym R25') R25)|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
    split; [rewrite X26; exact (eq_trans (eq_sym R26') R26)|].
    split; [rewrite X18, (dt_den_reg E 18 _ E18); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
    split; [rewrite X8; exact (eq_trans (eq_sym R8') R8)|].
    split; [rewrite X21, (dt_den_reg E 21 _ E21); reflexivity|].
    split; [rewrite X23; exact (eq_trans (eq_sym R23') R23)
           |rewrite X24; exact (eq_trans (eq_sym R24') R24)]. }
  split; [dt_reg HS (19%bv : bv 5) X19; rewrite X19; cbn [sv_denot]; reflexivity|].
  split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms0) md1 _ k1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
  split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hge|].
  split; [exact Hlater | exact Hbud].
- rewrite ((dt_bnez_room RG HGSB) E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_gt in Hc.
  pose proof HLINK as (Lcap & Lu & Lrest).
  assert (Hulen : ulen s1 = re_used e1)
    by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUlen).
  rewrite <- Lcap, Hulen in Hge. lia.
Qed.

Lemma dt_gx_open_xR : forall G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memc mdc k,
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi. exists memS. split; [exact HSTK|]. split; [exact Hag | exact HJi].
Qed.
Lemma dt_gx_close_xR : forall G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS HSTK Hag HJ.
apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS);
  [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha; lia].
Qed.

(* The rounds still to come ask for nonnegative sizes (dt_later_meters_x at R): W_drain_tr.v's dr_di_later_meters_xR
   projects the signs DI_xR gives along dlater. *)
Lemma dt_later_meters_xR : forall cx kr s1 D W1 c1 jb a tl,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DI_xR B PST ARx MT RP MMAX RG R cx [] kr s1 D W1 c1 ->
dlater cx (dgrow s1) jb a tl \/ dlater cx s1 jb a tl -> 0 <= tr_alloc tl /\ 0 <= tr_cost MT tl.
Proof.
intros cx kr s1 D W1 c1 jb a tl HB HI HL.
eapply W_drain_tr.dr_di_later_meters_xR; eassumption.
Qed.

Lemma dt_grow_core_xR : forall cx kr s1 (W1 : world SEGS) ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1
  (W2 : world SEGS) ly2 S2 mem2 md2 m3 md3 res nc,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 sent LB1 ->
DLINK s1 e1 h1 -> re_used e1 <= APARTIAL ->
drain_b_c.ds_cap (dgrow s1) = nc ->
nc = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) -> 8192 <= nc <= 16384 ->
AR0 ly2 S2 W2 mem2 md2 -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) nc ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
AJ0R cx ly2 S2 W2 m3 md3 (k1 + 3) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W2) mem2 x) ->
(forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) m3 x) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 16) 8 res ->
val_mem SEGS (arm W2 m3) (dxSA cx + 32) 8 nc ->
exists junk,
  DMEM0R cx ly2 S2 W2 m3 md3 (k1 + 3) (dt_ge e1 res nc junk) h1 (dgrow s1) out1 ev1 sent LB1 /\
  DLINK (dgrow s1) (dt_ge e1 res nc junk) h1.
Proof.
intros cx kr s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 W2 ly2 S2 mem2 md2 m3 md3 res nc
  HB HMEM HLINK Hused Enc Hncap Hnb HAR2 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ3 KV KP V16 V32.
pose proof asan_consts as (C1 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
pose proof HMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT &
  HLIVE & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (FB : alloc_ceiling + DRAIN_STK_x <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
assert (AR1 : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (AR3 : AR0 ly2 S2 W2 m3 md3) by (eapply ajournal_gx_AR_xR; exact HJ3).
pose proof HOKX as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HU & Hucap & HBUF & _ & HHP & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (HSAle' : dxSA cx + 56 <= dxG cx + 896) by (clear - HSAle; unfold AENT, ATABLE in HSAle; lia).
assert (Hcn : re_cap e1 <= nc /\ (nc = 8192 \/ nc = 16384)).
{ clear - Hncap Hnb Hcapv. destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq in Hncap; cbn [Z.eqb] in Hncap; lia. }
assert (RQN : req_size nc = nc) by (unfold req_size; destruct (Z.eqb_spec nc 0) as [E0|E0]; [lia | reflexivity]).
(* ---- the live blocks before and after the call ---- *)
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> 4096 <= re_buf e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1)).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (alx_blocks SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 _ _ AR1 Hin) as (_ & H4 & _). split; [exact H4 | exact Hin]. }
assert (Hnz' : re_cap e1 <> 0 -> re_buf e1 <> 0) by (intros Hc; destruct (Hnz Hc) as (H4 & _); lia).
pose proof ((dt_grow_perm B) ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res nc HPERM Hz Hnz' HpermA HpermB)
  as P2.
pose (TB := (dxG cx, ATABLE)).
pose (NB := (res, nc)).
pose (RB := asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).
pose (Q := dt_hkb e1 ++ RB).
change (Permutation (ablocks B ly2 S2) (NB :: TB :: Q)) in P2.
assert (P2T : Permutation (ablocks B ly2 S2) (TB :: NB :: Q))
  by (eapply Permutation_trans; [exact P2 | apply perm_swap]).
assert (P1 : Permutation (ablocks B ly1 S1) (TB :: (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ Q)).
{ eapply Permutation_trans; [exact HPERM|]. apply perm_skip.
  change (aentry_blks e1) with ((if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ dt_hkb e1).
  rewrite <- app_assoc. apply Permutation_refl. }
assert (Q1 : forall b, In b (TB :: Q) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P1)). destruct Hb as [<-|Hb]; [left; reflexivity|].
  right. apply in_or_app. right. exact Hb. }
assert (NB2 : In NB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); left; reflexivity).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2T)); left; reflexivity).
assert (Q2 : forall b, In b Q -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym P2)); right; right; exact Hb).
assert (DNB : forall b, In b (TB :: Q) -> zdisjoint (block_rng NB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head_x ly2 S2 [] W2 mem2 md2 NB (TB :: Q) b HAR2 P2 Hb)).
assert (DOB : re_cap e1 <> 0 -> forall b, In b (TB :: Q) ->
  zdisjoint (block_rng (re_buf e1, re_cap e1)) (block_rng b)).
{ intros Hc b Hb. apply (dt_sep_head_x ly1 S1 [] W1 m1 md1 _ (TB :: Q) b AR1); [|exact Hb].
  eapply Permutation_trans; [exact P1|]. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [app]. apply perm_swap. }
assert (DTQ : forall b, In b Q -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head_x ly2 S2 [] W2 mem2 md2 TB (NB :: Q) b HAR2 P2T (or_intror Hb))).
destruct (alx_blocks SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE AR1 (Q1 TB (or_introl eq_refl)))
  as (_ & HG4096 & HGceil & _).
rewrite RQT in HGceil.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 [] W2 m3 md3 res nc AR3 NB2) as (_ & HN4 & HNcl & _ & HNpr & _).
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 [] W2 m3 md3 (dxG cx) ATABLE AR3 TB2) as (_ & _ & _ & _ & HTpr & _).
rewrite RQN in HNcl, HNpr. rewrite RQT in HTpr.
(* ---- what the call keeps of the table and the entry's other blocks ---- *)
assert (KC : forall b x, In b (TB :: Q) -> fst b <= x < fst b + req_size (snd b) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) m1 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx. pose proof Hkept2 as (_ & K2 & _).
  replace x with (pb + (x - pb)) by ring. apply (K2 pb mb (x - pb) (Q1 _ Hb)); [lia|].
  replace (pb + (x - pb)) with x by ring. cbv beta.
  intros [Hn | (Hb0 & Ho)].
  - pose proof (DNB _ Hb) as Dj. unfold zdisjoint, block_rng, NB in Dj. cbn [fst snd] in Dj. lia.
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    pose proof (DOB Hc _ Hb) as Dj. unfold zdisjoint, block_rng in Dj. cbn [fst snd] in Dj. lia. }
(* ---- and what the stores keep ---- *)
assert (KO : forall b x, In b Q -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m3 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx.
  pose proof (DTQ _ Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj. rewrite RQT in Dj.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 [] W2 m3 md3 pb mb AR3 (Q2 _ Hb)) as (_ & H4 & Hcl & _ & Hpr & _).
  assert (Hr : 0 <= x < 2 ^ 64) by lia.
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x Hr N1 N2). exact (KC (pb, mb) x (or_intror Hb) Hx).
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (FK : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64)
    by (clear - Hx FB HAC; unfold DRAIN_STK_x, DRAIN_STK, SL_STK, SL_FRAME, DRAIN_FRAME, ASTACK in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x ltac:(lia) N1 N2). exact (K1 x Hr1 Hr2).
  - intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
    intros Hp. apply KP. exact (K5 x Hr1 Hr2 Hp). }
assert (NIMG : forall x, in_img SEGS x ->
  ~ (dxSA cx + 16 <= x < dxSA cx + 24) /\ ~ (dxSA cx + 32 <= x < dxSA cx + 40)).
{ intros x Hx. split; intros Hw;
    exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE x AR1 (Q1 TB (or_introl eq_refl))
      ltac:(rewrite RQT; lia) Hx). }
assert (APK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> apresent (w_H W1) m1 x -> apresent (w_H W2) m3 x).
{ intros x Hi Hno Herr Hp.
  assert (Hnot : forall ly0 S0 (W0 : world SEGS) m0 md0, AR0 ly0 S0 W0 m0 md0 -> ~ aowned B ly0 S0 x)
    by (intros ly0 S0 W0 m0 md0 HAx Ho; apply Hno;
        exact (proj1 (alx_owned_image SEGS B ARx LAWS ly0 S0 [] W0 m0 md0 x HAx Hi) Ho)).
  apply KP. apply (Hpres2 x Hi (Hnot _ _ _ _ _ AR1) (Hnot _ _ _ _ _ HAR2) Herr); [|exact Hp].
  intros [Hn | (Hb0 & Ho)].
  - exact (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 mem2 md2 res nc x HAR2 NB2 Hn Hi).
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 (re_buf e1) (re_cap e1) x AR1 (proj2 (Hnz Hc)) Ho Hi). }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  assert (Hi : in_img SEGS x) by exact (proj1 (HG x Hg)).
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  assert (EV : aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
  { rewrite (KV x Hr N1 N2). replace x with (as_errno B + (x - as_errno B)) by ring. apply Herr2.
    clear - Hx; lia. }
  split; [exact EV|]. intros _.
  apply (dt_img_wr RG); [exact Hi | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [exact (conj (proj1 (HG x Hx)) (proj1 (proj2 (HG x Hx)))) | exact (conj (proj1 (HGO x Hx)) (proj1 (proj2 (HGO x Hx))))]).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by lia.
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  pose proof Hkept2 as (_ & _ & K3 & _).
  split; [rewrite (KV x Hr N1 N2); exact (K3 x Hi Ho Hne)|].
  intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
  intros Hp. exact (APK x Hi Ho Hne Hp). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
assert (TK : forall x, dxSA cx <= x < dxSA cx + 56 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
  ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. rewrite (KV x ltac:(lia) N1 N2).
  apply (KC TB x (or_introl eq_refl)). unfold TB. cbn [fst snd]. rewrite RQT. lia. }
(* ---- the entry: the new buffer, its bytes and the 56 bytes at SA ---- *)
assert (CP3 : 0 < re_cap e1 -> forall i, 0 <= i < re_cap e1 ->
  aview SEGS (w_H W2) m3 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)).
{ intros Hc i Hi.
  pose proof (DNB TB (or_introl eq_refl)) as Dj. unfold zdisjoint, block_rng, NB, TB in Dj. cbn [fst snd] in Dj.
  rewrite RQT, RQN in Dj.
  rewrite (KV (res + i) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Hcopy; [destruct (Hnz ltac:(lia)) as (H4 & _); lia | rewrite Z.min_l by lia; exact Hi]. }
assert (HBUF' : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (destruct HBUF as [Hq|(Hq1 & _ & Hq3 & Hq4)]; [left; exact Hq | right; exact (conj Hq1 (conj Hq3 Hq4))]).
assert (Hcb : 0 <= re_cap e1 <= nc) by (destruct Hcapv as [Hq|[Hq|Hq]]; lia).
destruct ((dt_newbuf RG HGSB) W1 m1 W2 m3 e1 res nc HBUF' HU Hcb CP3 (fun x Hx => proj1 (HNpr x Hx)))
  as (junk & Hjl & Hjg).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
assert (Hnc64 : 0 <= nc < 2 ^ 64) by lia.
assert (ENT3 : garr8 SEGS (arm W2 m3) (dxSA cx) (bzs (entry_bytes (dt_ge e1 res nc junk)))).
{ apply ((dt_entry_grow RG HGSB) W1 m1 W2 m3 (dxSA cx) e1 res nc junk Hp1 Hres64 Hnc64 HENTB V16 V32); [| | | exact Hp2];
    intros x Hx; apply TK; lia. }
assert (AWR3 : awr W2 m3 (dxSA cx) AENT).
{ intros i Hi. apply (apresent_writable SEGS).
  apply (proj1 (HTpr (dxSA cx + i) ltac:(unfold AENT in Hi; lia))). }
assert (AK : akept W1 m1 W2 m3 (gfp (re_hp e1) (bzs (key_ptrs (re_keys e1))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e1))).
{ intros r Hr x Hx. destruct Hr as [<- | Hr].
  - unfold gfp in Hx. cbn [fst snd] in Hx. rewrite dt_bzs_len, (dt_key_ptrs_len RG) in Hx.
    destruct HHP as [(Hz0 & Hk0) | (Hz0 & HinH & Hk1 & Hk2 & _)].
    + rewrite Hk0 in Hx. cbn [length] in Hx. lia.
    + apply (KO (re_hp e1, re_kh e1) x).
      * unfold Q, dt_hkb. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz0).
        apply in_or_app. left. left. reflexivity.
      * cbn [fst snd]. unfold re_nheld in Hk1. pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & RQ). lia.
  - apply in_map_iff in Hr as (k & <- & Hk).
    apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
    + unfold Q, dt_hkb. apply in_or_app. left. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    + unfold gfp in Hx. cbn [fst snd] in Hx |- *. rewrite dt_bzs_len, length_app in Hx. cbn [length] in Hx.
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & RQ). lia. }
assert (OKX3 : aentry_okx B ly2 S2 W2 m3 (dt_ge e1 res nc junk)).
{ apply ((dt_aentry_okx_grow B RG) ly1 S1 W1 m1 ly2 S2 W2 m3 e1 res nc junk HOKX (proj2 Hcn)
    ltac:(unfold APARTIAL in Hused; lia) NB2 Hjl Hjg AK).
  intros b Hb. apply Q2. unfold Q. apply in_or_app. left. exact Hb. }
(* ---- the harness source, the other slots, g_s, the output ---- *)
assert (SRC3 : asrc_at B ly2 S2 W2 m3 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m3 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. destruct ((dt_src_fp B RG HGSB) ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. unfold Q, RB. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - intros b Hb. apply Q2. unfold Q, RB. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (OTH3 : aothers_at RG W2 m3 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & Va & Vb & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m3) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact Va] | split; [apply GV; [| | exact Vb] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK3 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m3 x)
  by (intros x H1 H2; exact (dt_bk_trans _ _ W1 m1 W2 m3 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT3 : aout_at B RG ly2 S2 W2 m3 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m3 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct ((dt_out_fp B RG) _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, drain_b_c.ds_ocap s1) x).
    + unfold Q, RB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply Q2. unfold Q, RB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (ROM3 : rom_view SEGS W2 m3).
{ intros x Hx. destruct (HROMO x Hx) as (_ & Hpin & Hne & _).
  destruct (Exists_dec (in_zr x) (as_owned_static B) ((dt_in_zr_dec RG) x)) as [Hown | Hno].
  - eapply (rom_pinned_view_x SEGS B ARx LAWS); [exact AR3 | exact (Hpin Hown)].
  - assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    destruct (NIMG x Hi) as (N1 & N2).
    assert (Hr : 0 <= x < 2 ^ 64)
      by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
    pose proof Hkept2 as (_ & _ & K3 & _).
    rewrite (KV x Hr N1 N2), (K3 x Hi Hno Hne). exact (HROM x Hx). }
assert (PK3 : apres_kept B (dxW cx) (dxmem cx) W2 m3)
  by (intros x Hi Ho He Hp; exact (APK x Hi Ho He (HPRESK x Hi Ho He Hp))).
assert (EA2 : aentry_blks (dt_ge e1 res nc junk) = NB :: dt_hkb e1).
{ unfold aentry_blks, dt_ge, dt_hkb. cbn [re_cap re_buf re_hp re_kh re_keys].
  rewrite (proj2 (Z.eqb_neq nc 0) ltac:(lia)). reflexivity. }
exists junk. split.
- unfold DMEM_xR.
  refine (conj HJ3 (conj ROM3 (conj PK3 (conj (eq_trans Hfrs2 HFRM) (conj ((dt_frame_kept RG HGSB) cx W1 m1 W2 m3 FK HFRAME)
    (conj ENT3 (conj AWR3 (conj OKX3 (conj SRC3 (conj OTH3 (conj GSK3 (conj OUT3 (conj HLIVE _))))))))))))).
  rewrite EA2. exact P2T.
- pose proof HLINK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  refine (conj (eq_sym Enc) (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10
    (conj K11 K12))))))))))).
Qed.

Lemma dt_grow_post_xR : forall cx kr s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl
  memS (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 res tl2,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 8 = w64 ((rg_s RG + 4) / 8) -> getr regs1 9 = w64 (rg_s RG / 8) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 18 = w64 (rg_s RG) -> getr regs1 19 = w64 384 ->
getr regs1 20 = w64 (drain_b_c.ds_cap (dgrow s1)) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 23 = w64 (shadow_addr (dxSA cx + 32)) ->
getr regs1 24 = w64 (shadow_addr (dxSA cx)) -> getr regs1 25 = w64 (dxSA cx + 32) ->
getr regs1 26 = w64 (dxSA cx + 16) -> getr regs1 27 = w64 (dxSA cx + 24) ->
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud0 cx kr ly1 S1 spent tl ->
4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1) ->
drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) ->
8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384 ->
tl = fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)) ++ tl2 ->
dlater cx (dgrow s1)
  (jb + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa))))
  (agrow s1 jb aa) tl2 ->
0 <= DRAIN_STK_x -> gagree (G_DR B RG) (w_H (dxW cx)) (dxmem cx) memS ->
ajournal_xR SEGS B PST ARx R DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) memS (dxmd cx) []
  ly2 S2 Hp2 W2 mem2 md2 (k1 + 3) ->
aregs_preserved regs1 regs2 -> getr regs2 10 = w64 res -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2)
   ((res, drain_b_c.ds_cap (dgrow s1)) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, drain_b_c.ds_cap (dgrow s1)) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
            (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
mo_le MT S1 S2 (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT) ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk tl2) + kr) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
      (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
(forall W3 c3, DT1_xR cx kr (dgrow s1) D W3 c3 -> YA0nH.SRrG SEGS R W3 c3 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W2 (mkCfg (mkst regs2 (w64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)) md2)
  (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS W2 ly2 S2 Hp2 regs2 mem2 md2
  res tl2 HB Hsp Hra R3 R4 R8 R9 R10 R11 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2i HPR Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 HRM2 Herr2 Hpres2 K.
assert (EHp2 : Hp2 = []) by (eapply HP0; exact (proj1 HJ2i)). subst Hp2.
destruct Hbud as (Hbud & HRM1 & HCNT1).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR1 : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by exact (proj1 HJ2i).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR1 HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
(* the blocks after the call: the table is still live, the new block is (res, nc) *)
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HUl & Hucap & HBUF & _).
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> re_buf e1 <> 0).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 _ _ HAR1 Hin) as (_ & H4 & _). lia. }
pose proof ((dt_grow_perm B) ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res (drain_b_c.ds_cap (dgrow s1))
  Hperm Hz Hnz HpermA HpermB) as HP2.
assert (TB2 : In (dxG cx, ATABLE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); right; left; reflexivity).
assert (NB2 : In (res, drain_b_c.ds_cap (dgrow s1)) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 mem2 md2 _ _ HAR2 NB2) as (_ & _ & HNcl & _).
pose proof (req_size_pos (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)) as (_ & RQN).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 mem2 md2 (dxG cx) ATABLE HAR2 TB2) as (_ & _ & _ & _ & HTP2 & _).
(* the frame across the call: realloc keeps every byte above its stack window *)
assert (FK0 : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 mem2 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64) by (clear - Hx HspA HspB; unfold DRAIN_FRAME in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  split; [exact (K1 x Hr1 Hr2)|]. intros Hw.
  apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 mem2 x); [|exact Hw]. exact (K5 x Hr1 Hr2). }
pose proof ((dt_frame_kept RG HGSB) cx W1 m1 W2 mem2 FK0 HFR) as HFR2.
pose proof HFR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F216' & _).
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
{ intros r Hr. pose proof (HPR (bv_unsigned r) Hr) as Q. rewrite Z_to_bv_bv_unsigned in Q. exact Q. }
assert (P2 : getr regs2 2 = getr regs1 2) by (apply PR; dt_cs).
assert (P8 : getr regs2 8 = getr regs1 8) by (apply PR; dt_cs).
assert (P9 : getr regs2 9 = getr regs1 9) by (apply PR; dt_cs).
assert (P18 : getr regs2 18 = getr regs1 18) by (apply PR; dt_cs).
assert (P21 : getr regs2 21 = getr regs1 21) by (apply PR; dt_cs).
assert (P22 : getr regs2 22 = getr regs1 22) by (apply PR; dt_cs).
assert (P23 : getr regs2 23 = getr regs1 23) by (apply PR; dt_cs).
assert (P24 : getr regs2 24 = getr regs1 24) by (apply PR; dt_cs).
assert (P25 : getr regs2 25 = getr regs1 25) by (apply PR; dt_cs).
assert (P26 : getr regs2 26 = getr regs1 26) by (apply PR; dt_cs).
assert (P27 : getr regs2 27 = getr regs1 27) by (apply PR; dt_cs).
assert (P3 : getr regs2 3 = getr regs1 3) by (apply PR; dt_cs).
assert (P4 : getr regs2 4 = getr regs1 4) by (apply PR; dt_cs).
assert (P19 : getr regs2 19 = getr regs1 19) by (apply PR; dt_cs).
assert (P20 : getr regs2 20 = getr regs1 20) by (apply PR; dt_cs).
unfold w64.
remember (Eimg (Ereg regs2 (dt_gp_extra (dxSA cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ n r Hr)).
assert (E2 : ew E 2 = getr regs2 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs2 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs2 4) by (apply EREG; [lia | reflexivity]).
assert (E19 : ew E 19 = getr regs2 19) by (apply EREG; [lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 (drain_b_c.ds_cap (dgrow s1)))
  by (rewrite (EREG 20%nat 20%bv) by (first [lia | reflexivity]); rewrite P20; exact R20).
assert (E10 : ew E 10 = Z_to_bv 64 res)
  by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact Hres10).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); rewrite P18; exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite P21; exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2, P2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (R22' : getr regs2 22 = sv_denot E (SOff 32 0))
  by (rewrite P22, (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs2 25 = sv_denot E (SOff 32 32))
  by (rewrite P25, (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs2 26 = sv_denot E (SOff 32 16))
  by (rewrite P26, (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs2 27 = sv_denot E (SOff 32 24))
  by (rewrite P27, (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs2 23 = sv_denot E (dt_sh 32 32))
  by (rewrite P23, ((dt_den_sh RG) E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs2 24 = sv_denot E (dt_sh 32 0))
  by (rewrite P24, ((dt_den_sh RG) E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs2 9 = sv_denot E (dt_gv 0))
  by (rewrite P9, ((dt_den_gv RG) E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs2 8 = sv_denot E (dt_gv 4))
  by (rewrite P8, ((dt_den_gv RG) E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_gp
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gp. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gp_frame, dt_gp_buf, dt_gp_cap;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
        [ exact ((dt_den_sh RG) E 32 (dxSA cx) 16 E32 E21 ltac:(lia) ltac:(lia))
        | unfold shadow_addr, SHADOW_OFF;
          (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                  | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia); zside])
        | zside
        | exact F216' ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
  - apply pairwise_disjoint_of_extents. unfold dt_gp_frame, dt_gp_buf, dt_gp_cap, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gp_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W2) mem2)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub_x ly2 S2 W2 mem2 md2 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR2 TB2).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
pose proof (dt_gx_close_xR (G_DR B RG) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 [] W2 mem2 md2 (k1 + 3) memS HSTK HAG HJ2i) as HJ2.
psrr_branch_tok RUNR BRR HS SHOK DBspan.
- (* beqz a0 taken: res = 0, but the rule's res is at least 4096 *)
  exfalso. rewrite ((dt_beqz_atom RG) E 10 res E10 Hres64) in Hc. apply Z.eqb_eq in Hc. lia.
- paj_run_to_tok_xR RUNTOR HS HJ2 SHOK DBspan A_dr_mid.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa0 Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_nil. }
  rewrite ?wvb_collapse in HJ2.
  (* the stretch wrote s->buf and s->cap only, and kept every byte's presence *)
  assert (Hnw : forall x, ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
    ~ in_wrange E (ss_mem ss_gp) x).
  { intros x N1 N2 (r & Hin & Hr). cbv [ss_mem ss_gp dt_gp_frame dt_gp_buf dt_gp_cap] in Hin.
    destruct Hin as [Hq|[Hq|[Hq|[]]]]; subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?U32 in Hr; lia. }
  assert (KV : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
    ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W2) mem2 x)
    by (intros x Hx N1 N2; exact (aview_kept_out E _ (w_H W2) mem2 (ms_mem ms) HFr x Hx (Hnw x N1 N2))).
  assert (KP : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem ms) x)
    by (intros x Hx; exact (apresent_grows _ _ _ _ HG0 Hx)).
  (* the two stored cells *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RB.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RC.
  cbn [ms_mem restrict] in RB, RC.
  assert (V16 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 16) 8 res).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 16 8%N (SOff 10 0) res RB U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 10 res E10 Hres64).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V32 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 32) 8 (drain_b_c.ds_cap (dgrow s1))).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 32 8%N (SOff 20 0) (drain_b_c.ds_cap (dgrow s1))
      RC U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 20 (drain_b_c.ds_cap (dgrow s1)) E20 ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
  dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (18%bv : bv 5) X18.
  dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21. dt_reg HS (22%bv : bv 5) X22.
  dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
  dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
  pmkst HS.
  (* the model side: the growth's request and the meter *)
  pose proof HLINK as (Lcap & Lu & Lrest).
  assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUl).
  destruct ((dt_grow_ev MT RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
    ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
  change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
  assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
  { pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)).
    pose proof (mo_free_nonneg MT MTL). lia. }
  assert (Hb0 : re_buf e1 = 0 -> re_cap e1 = 0)
    by (intros Hb; destruct (Z.eq_dec (re_cap e1) 0) as [Hq|Hq]; [exact Hq | exfalso; exact (Hnz Hq Hb)]).
  pose proof ((dt_grow_bbx B RG) ly1 S1 ly2 S2 e1 res (drain_b_c.ds_cap (dgrow s1)) Hb0 HpermA HpermB) as HBB.
  assert (HBB2 : blocks_bytes S2 + tr_peak tl2 <= LIVE_MAX).
  { pose proof Hbud as (_ & _ & _ & Hlv & _). rewrite Htl in Hlv.
    destruct ((dt_grow_pk RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
      ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlv) as (_ & Hpk).
    change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hpk.
    rewrite <- Lcap in Hpk. lia. }
  pose proof ((dt_grow_bud MT MMAX RG MTL HGSB) cx S1 S2 spent tl tl2 _ (drain_b_c.ds_cap (dgrow s1)) Hbud Htl Hev_co Hev_max
    HmoN Hmle2 HBB2) as HBUD2.
  (* the room round: the counts after the request, at the tail's peak *)
  assert (HCNT2 : cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl2) + 2)%nat) (ablocks B ly2 S2)).
  { eapply (cnt_ok_pk_mono RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl) + 2)%nat) _ (ablocks B ly1 S1) _);
      [|exact HCNT1].
    intros P. cbv beta.
    assert (Htl' : tl = fst (drain_b_c.grow_tr (re_cap e1) (re_used e1) jb (drain_b_c.da_buf aa)) ++ tl2)
      by (rewrite Lcap, <- Hulen; exact Htl).
    pose proof (dt_grow_cnt ly1 S1 ly2 S2 (re_buf e1) (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) res (re_used e1) jb
      (drain_b_c.da_buf aa) tl2 P ltac:(rewrite Lcap, <- Hulen; exact Hlt) Hncap Hz Hnz HpermA HpermB) as Hcn.
    rewrite <- Htl' in Hcn.
    pose proof (ReplyCnt.tr_peakP_nonneg _ P tl2). pose proof (ReplyCnt.tr_peakP_nonneg _ P tl). lia. }
  (* the memory core *)
  destruct (dt_grow_core_xR cx kr s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 W2 ly2 S2 mem2 md2
    (ms_mem ms) _ res (drain_b_c.ds_cap (dgrow s1)) HB HMEM HLINK Hused eq_refl Hncap Hnb HAR2 Hfrs2 Hres4096
    HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ2 KV KP V16 V32) as (junk & HDM & HDL).
  (* the cut *)
  apply K. unfold DT1_xR.
  eexists _, ly2, S2, _, _, (k1 + 3), (dt_ge e1 res (drain_b_c.ds_cap (dgrow s1)) junk), h1, out1, ev1, LB1,
    (spent + (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT)), _, (agrow s1 jb aa), tl2.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2), P2; exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3), P3; exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4), P4; exact R4|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') (eq_trans P22 R22))|].
    split; [rewrite X25; exact (eq_trans (eq_sym R25') (eq_trans P25 R25))|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') (eq_trans P27 R27))|].
    split; [rewrite X26; exact (eq_trans (eq_sym R26') (eq_trans P26 R26))|].
    split; [rewrite X18, (dt_den_reg E 18 _ E18); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') (eq_trans P9 R9))|].
    split; [rewrite X8; exact (eq_trans (eq_sym R8') (eq_trans P8 R8))|].
    split; [rewrite X21, (dt_den_reg E 21 _ E21); reflexivity|].
    split; [rewrite X23; exact (eq_trans (eq_sym R23') (eq_trans P23 R23))
           |rewrite X24; exact (eq_trans (eq_sym R24') (eq_trans P24 R24))]. }
  split; [rewrite X19, (dt_den_reg E 19 _ E19), P19; exact R19|].
  split; [exact HDM|].
  split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HDL|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
  split; [exact Hlater2|]. split; [exact HBUD2|]. split; [exact HRM2 | exact HCNT2].
Qed.

Lemma dt_grow_after_xR : forall cx kr s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl c0,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DI_xR B PST ARx MT RP MMAX RG R cx [] kr s1 D W1 c0 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 8 = w64 ((rg_s RG + 4) / 8) -> getr regs1 9 = w64 (rg_s RG / 8) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 18 = w64 (rg_s RG) -> getr regs1 19 = w64 384 ->
getr regs1 20 = w64 (drain_b_c.ds_cap (dgrow s1)) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 23 = w64 (shadow_addr (dxSA cx + 32)) ->
getr regs1 24 = w64 (shadow_addr (dxSA cx)) -> getr regs1 25 = w64 (dxSA cx + 32) ->
getr regs1 26 = w64 (dxSA cx + 16) -> getr regs1 27 = w64 (dxSA cx + 24) ->
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud0 cx kr ly1 S1 spent tl ->
(forall W2 c2, DT1_xR cx kr (dgrow s1) D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (SIGMA WS_realloc)) m1 (seg_rom SEGS)) md1)
  (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl c0 HB HDI
  Hsp Hra R3 R4 R8 R9 R10 R11 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud0 K.
pose proof Hbud0 as (Hbud & HRM1 & HCNT1).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & Hgarr0 & Hawr0 & HEOK0 & Hj4 & Hsrc0 & Hoth0 & HfdB &
  Hskip0 & HU0 & Hout0 & Hrom0 & Hperm0 & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hcapv : re_cap e1 = 0 \/ re_cap e1 = 8192 \/ re_cap e1 = 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); lia).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hroom : 4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1)).
{ apply (dt_grow_room RG HGSB); [exact Hlt | rewrite Hulen; unfold APARTIAL in Hused |- *; lia
  | rewrite Hulen, <- Lcap; exact Hucap | rewrite <- Lcap; exact Hcapv ]. }
assert (Hncap : drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2)).
{ change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
  rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; exact Hucap) Hlt),
    <- Lcap. reflexivity. }
assert (Hnb : 8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384)
  by (rewrite Hncap; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; cbn [Z.eqb];
      [lia | lia | unfold APARTIAL in Hused; lia]).
(* what the growth asks of the allocator *)
destruct ((dt_grow_tr RG HGSB) cx s1 jb aa tl Hlater Hroom) as (tl2 & Htl & Hlater2).
destruct (dt_later_meters_xR cx kr s1 D W1 c0 _ _ tl2 HB HDI (or_introl Hlater2)) as (_ & Hco2).
(* the room the request needs (2 for it, the tail's charge on top of kr after it) *)
assert (HRMc : rp_RM RP S1 (2 + (Z.to_nat (tr_cost MT_rk tl2) + kr))).
{ pose proof HRM1 as H. rewrite Htl in H. exact (dt_grow_room_rk S1 _ _ _ _ tl2 kr Hlt H). }
destruct ((dt_grow_ev MT RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
  ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
pose proof Hbud as (Hmle & Hspent & Hcost & Hlive & Hmax).
rewrite Htl, (dt_tr_max_app RG HGSB), Hev_max in Hmax.
rewrite Htl in Hlive.
destruct ((dt_grow_pk RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
  ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlive) as (Hlv1 & _).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hlv1.
rewrite Htl, (dt_tr_cost_app MT RG), Hev_co in Hcost.
assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
{ pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)).
  pose proof (mo_free_nonneg MT MTL). lia. }
(* the buffer the round hands over *)
assert (Hbufc : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\
   Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hpn : re_buf e1 = 0 \/ In (re_buf e1, re_cap e1) (ablocks B ly1 S1))
  by (destruct Hbufc as [(_ & Hq & _)|(_ & Hq & _)]; [left; exact Hq | right; exact Hq]).
destruct (dt_gx_open_xR (G_DR B RG) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 [] W1 m1 md1 k1 HJ) as (memS & HSTK & HAG & HJi).
(* the meter premise of the call, which the rule's HA premise also takes *)
assert (HMO : mo_ok MT S1 (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT)).
{ apply ((dt_mo_ok_of MT MMAX RG MTL HGSB) cx S1 spent tl);
    [ exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HBrest)))))) | exact Hbud | exact HmoN|].
  rewrite Htl, (dt_tr_cost_app MT RG), Hev_co. lia. }
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (AREALLOC_R W1 regs1 m1 DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) memS (dxmd cx) []
    ly1 S1 [] md1 k1 (re_buf e1) (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) (- DRAIN_FRAME)
    (w64 (BASE + A_dr_rret)) [] (Z.to_nat (tr_cost MT_rk tl2) + kr)%nat HJi).
  - exact Hpn.
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - unfold cnt_ok.
    eapply (cnt_ok_pk_mono RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl) + 2)%nat) (fun _ => 0%nat)
      (ablocks B ly1 S1) (ablocks B ly1 S1)); [intros P; cbv beta; lia | exact HCNT1].
  - unfold DRAIN_FRAME in *. lia.
  - reflexivity.
  - unfold DRAIN_FRAME. lia.
  - assert (Hq : ASTACK - - DRAIN_FRAME <= DRAIN_STK_x) by (vm_compute; discriminate). exact Hq.
  - eapply aj_stack_room_xR with (o := - DRAIN_FRAME);
      [exact HJi | unfold DRAIN_FRAME in *; lia | vm_compute; discriminate].
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact Hra.
  - unfold w64. apply ret_ok_codeptr_v; [unfold A_dr_rret, AF_fr_drain; lia
    | unfold A_dr_rret, AF_fr_drain; reflexivity].
  - apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] regs1).
    + apply achain_low. assert (Hq : (rg_s RG + 4) / 8 <= rg_s RG + 4) by (apply Z.div_le_upper_bound; lia).
      lia.
    + unfold DRAIN_FRAME in *. lia.
    + unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
      assert (Hq : (rg_s RG + 4) / 8 <= rg_s RG + 4) by (apply Z.div_le_upper_bound; lia).
      assert (Hq2 : 0 <= (rg_s RG + 4) / 8) by (apply Z.div_pos; lia). lia.
    + unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small
        by (unfold A_dr_rret, AF_fr_drain; lia). unfold A_dr_rret, AF_fr_drain. lia.
  - exact (RO_ARx _ _ _ _ _ _ HAR).
  - exact (HA_call _ _ _ _ _ _ HMO).
  - cbn [spine]. replace (raZ regs1) with (BASE + AF_fr_drain + 0x170); [exact HCTX_re1|].
    unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small
      by (unfold A_dr_rret, AF_fr_drain; lia). unfold A_dr_rret. lia.
  - exact HRMc.
  - intros Hp0 Hin0 i Hi.
    assert (Hcap0 : 0 < re_cap e1)
      by (destruct Hbufc as [(_ & Hq & _)|(Hq & _)]; [contradiction | lia]).
    assert (Hinbl : In (re_buf e1, re_cap e1) (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1)).
    { apply in_or_app. left. unfold aentry_blks.
      assert (Ec : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Ec. left. reflexivity. }
    apply (dt_buf_fp_x cx ly1 S1 [] W1 m1 md1 (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1) (re_buf e1) (re_cap e1) HAR);
      [ (try rewrite <- !app_assoc); exact Hperm | exact Hinbl
      | (try rewrite <- !app_assoc); exact Hperm0 | exact Hin0 | lia
      | unfold ATABLE; lia | exact Hi ].
  - exact HMO. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc2 & HJ2 & Hpres' & Hres10 & Hfrs2 &
  Hres4096 & HpermA & HpermB & Hcopy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
subst c2.
exact (dt_grow_post_xR cx kr s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS
  W2 ly2 S2 Hp2 regs2 mem2 md2 res tl2 HB Hsp Hra R3 R4 R8 R9 R10 R11 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud0 Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2 Hpres' Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 HRM2 Herr2 Hpres2 K).
Qed.

Lemma dt_grow_xR : forall cx kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DI_xR B PST ARx MT RP MMAX RG R cx [] kr s1 D W1 c1 ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
(forall W2 c2, DT1_xR cx kr (dgrow s1) D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr s1 D W1 c1 HB HDI Hlt K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDI as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
dt_hp1R HMEM Hp1.
pose proof Hregs as (Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 &
  F224 & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & Hq & _); exact Hq).
assert (Hcapb : 0 <= re_cap e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hl & _); lia).
assert (Hbufb : 0 <= re_buf e1 /\ re_buf e1 + re_cap e1 <= alloc_ceiling).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _).
  destruct Hq as [(Hc & Hb & Hu)|(Hc & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hin) as (_ & H4 & Hcl & _).
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq). lia. }
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_gr_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs1 25 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs1 26 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs1 23 = sv_denot E (dt_sh 32 32))
  by (rewrite ((dt_den_sh RG) E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs1 24 = sv_denot E (dt_sh 32 0))
  by (rewrite ((dt_den_sh RG) E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs1 8 = sv_denot E (dt_gv 4))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_gr
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gr. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gr_frame, dt_gr_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 16 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 24 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F224 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 35 0) (re_buf e1));
          [exact (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_buf RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_used RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_cap RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_gr_frame, dt_gr_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gr_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub_x ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUNR BRR HS SHOK DBspan.
- (* 4096 <= cap - used: not this arm *)
  rewrite ((dt_bnez_room RG HGSB) E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_le in Hc. rewrite <- Lcap, Hulen in Hlt. lia.
- paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  psrr_branch_tok RUNR BRR HS SHOK DBspan.
  all: rewrite ((dt_bnez_atom RG) E 33 (re_cap e1) E33 ltac:(lia)) in Hc0.
  + (* the entry has a buffer: the round asks for twice its capacity *)
    apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = re_cap e1 * 2).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap. apply Z.eqb_neq in Hc0. rewrite Hc0. reflexivity. }
    dt_reg HS (1%bv : bv 5) X1. dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3.
    dt_reg HS (4%bv : bv 5) X4. dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9.
    dt_reg HS (10%bv : bv 5) X10. dt_reg HS (11%bv : bv 5) X11. dt_reg HS (18%bv : bv 5) X18.
    dt_reg HS (19%bv : bv 5) X19. dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
    dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    eapply (dt_grow_after_xR cx kr s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl _ HB HDI).
    all: first
      [ (unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp)
      | (rewrite X1; change 240%nat with A_TEXT; rewrite (codeptr_val E 3936 HEI);
         unfold w64, A_dr_rret, AF_fr_drain; f_equal; lia)
      | (rewrite X3, (dt_den_reg E 3 _ E3); exact R3)
      | (rewrite X4, (dt_den_reg E 4 _ E4); exact R4)
      | (rewrite X8; exact (eq_trans (eq_sym R8') R8))
      | (rewrite X9; exact (eq_trans (eq_sym R9') R9))
      | (rewrite X10, (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)); reflexivity)
      | (rewrite X11, ((dt_den_sll RG HGSB) E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc; reflexivity)
      | (rewrite X18, (dt_den_reg E 18 _ E18); reflexivity)
      | (rewrite X19; cbn [sv_denot]; reflexivity)
      | (rewrite X20, ((dt_den_sll RG HGSB) E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc; reflexivity)
      | (rewrite X21, (dt_den_reg E 21 _ E21); reflexivity)
      | (rewrite X22; exact (eq_trans (eq_sym R22') R22))
      | (rewrite X23; exact (eq_trans (eq_sym R23') R23))
      | (rewrite X24; exact (eq_trans (eq_sym R24') R24))
      | (rewrite X25; exact (eq_trans (eq_sym R25') R25))
      | (rewrite X26; exact (eq_trans (eq_sym R26') R26))
      | (rewrite X27; exact (eq_trans (eq_sym R27') R27))
      | exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
          (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      | exact HnoNUL | exact Hused | exact HLINK | exact HSAME | exact HHIST | exact HJ1
      | exact Hlt | exact Hlater | exact Hbud | exact K ].
  + (* no buffer yet: the round asks for 8192 *)
    apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = 8192).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap, Hc0. reflexivity. }
    dt_reg HS (1%bv : bv 5) X1. dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3.
    dt_reg HS (4%bv : bv 5) X4. dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9.
    dt_reg HS (10%bv : bv 5) X10. dt_reg HS (11%bv : bv 5) X11. dt_reg HS (18%bv : bv 5) X18.
    dt_reg HS (19%bv : bv 5) X19. dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
    dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    eapply (dt_grow_after_xR cx kr s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl _ HB HDI).
    all: first
      [ (unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp)
      | (rewrite X1; change 240%nat with A_TEXT; rewrite (codeptr_val E 3936 HEI);
         unfold w64, A_dr_rret, AF_fr_drain; f_equal; lia)
      | (rewrite X3, (dt_den_reg E 3 _ E3); exact R3)
      | (rewrite X4, (dt_den_reg E 4 _ E4); exact R4)
      | (rewrite X8; exact (eq_trans (eq_sym R8') R8))
      | (rewrite X9; exact (eq_trans (eq_sym R9') R9))
      | (rewrite X10, (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)); reflexivity)
      | (rewrite X11, Hnc; cbn [sv_denot]; reflexivity)
      | (rewrite X18, (dt_den_reg E 18 _ E18); reflexivity)
      | (rewrite X19; cbn [sv_denot]; reflexivity)
      | (rewrite X20, Hnc; cbn [sv_denot]; reflexivity)
      | (rewrite X21, (dt_den_reg E 21 _ E21); reflexivity)
      | (rewrite X22; exact (eq_trans (eq_sym R22') R22))
      | (rewrite X23; exact (eq_trans (eq_sym R23') R23))
      | (rewrite X24; exact (eq_trans (eq_sym R24') R24))
      | (rewrite X25; exact (eq_trans (eq_sym R25') R25))
      | (rewrite X26; exact (eq_trans (eq_sym R26') R26))
      | (rewrite X27; exact (eq_trans (eq_sym R27') R27))
      | exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
          (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      | exact HnoNUL | exact Hused | exact HLINK | exact HSAME | exact HHIST | exact HJ1
      | exact Hlt | exact Hlater | exact Hbud | exact K ].
Qed.

Definition DSC_xR (cx : dcx) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (i : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_scan) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 27 = w64 (dxSA cx + 24) /\ getr regs1 26 = w64 (dxSA cx + 16) /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
getr regs1 14 = w64 (re_fd e1) /\ getr regs1 12 = w64 (96 * Z.of_nat i) /\
getr regs1 19 = w64 384 /\ getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat i) /\
(i <= dxj cx)%nat /\
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud0 cx kr ly1 S1 spent tl.

Lemma dt_scan_step_xR : forall cx kr sg D i W1 c1,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DSC_xR cx kr sg D i W1 c1 ->
(forall W2 c2, DSC_xR cx kr sg D (S i) W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
(forall W2 c2, DT2_xR B PST ARx MT RP MMAX RG R cx [] kr sg D W2 c2 ->
   YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr sg D i W1 c1 HB HDSC Knext Kfound.
destruct HDSC as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R10 & R13 & R14 & R12 & R19 & R24 &
  Hij & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (Hfdv : 0 <= re_fd e1 < 2 ^ 31) by (pose proof HEOK as (_ & _ & _ & _ & Hq & _); exact Hq).
assert (Hi4 : (i < 4)%nat) by (pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _); lia).
subst c1. unfold cfg_at, w64.
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & Hgarr0 & Hawr0 & HEOK0 & Hj4 & Hsrc0 & Hoth0 & HfdB &
  HBrest).
pose proof HSAME as (Sfd & Seof & Shfd & Shopen & HSrest).
assert (Hfd : hs_fd h1 = re_fd e1) by (rewrite Shfd, HfdB; exact (eq_sym Sfd)).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
(* the four slots of g_s, as the scan reads them *)
assert (Hslot : forall ii, (ii < 4)%nat -> exists f o,
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii) 4 f /\
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii + 4) 4 o /\
  0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32 /\
  (ii = dxj cx -> f = re_fd e1 /\ o <> 0) /\
  (ii <> dxj cx -> o = 0 \/ f <> re_fd e1)).
{ intros ii Hii. destruct (Nat.eq_dec ii (dxj cx)) as [->|Hne].
  - pose proof Hsrc as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    unfold dHA, ASRC in V1, V2.
    exists (hs_fd h1), (hs_open h1).
    split; [exact V1|]. split; [exact V2|]. split; [lia|]. split; [rewrite Hopen; lia|].
    split; [intros _; split; [exact Hfd | rewrite Hopen; lia]|]. intros Hcc; contradiction.
  - assert (HfdvX : 0 <= re_fd (dxe cx) < 2 ^ 31) by (rewrite <- Sfd; exact Hfdv).
    destruct ((dt_others_canon RG HGSB) W1 m1 (dxj cx) (re_fd (dxe cx)) ii Hoth Hii Hne HfdvX)
      as (f & o & V1 & V2 & Bf & Bo & Hdis).
    unfold ASRC in V1, V2.
    exists f, o. split; [exact V1|]. split; [exact V2|]. split; [exact Bf|]. split; [exact Bo|].
    split; [intros Hcc; contradiction|]. intros _. rewrite Sfd.
    destruct Hdis as [Hq|Hq]; [left; exact Hq|right].
    rewrite (Z.mod_small f (2 ^ 32)) in Hq by lia.
    rewrite (Z.mod_small (re_fd (dxe cx)) (2 ^ 32)) in Hq by lia. exact Hq. }
destruct (Hslot 0%nat ltac:(lia)) as (f0 & o0 & V00 & V01 & B00 & B01 & Hjj0 & Hoo0).
destruct (Hslot 1%nat ltac:(lia)) as (f1 & o1 & V10 & V11 & B10 & B11 & Hjj1 & Hoo1).
destruct (Hslot 2%nat ltac:(lia)) as (f2 & o2 & V20 & V21 & B20 & B21 & Hjj2 & Hoo2).
destruct (Hslot 3%nat ltac:(lia)) as (f3 & o3 & V30 & V31 & B30 & B31 & Hjj3 & Hoo3).
replace (rg_s RG + 96 * Z.of_nat 0) with (rg_s RG) in V00 by lia.
replace (rg_s RG + 96 * Z.of_nat 0 + 4) with (rg_s RG + 4) in V01 by lia.
replace (rg_s RG + 96 * Z.of_nat 1) with (rg_s RG + 96) in V10 by lia.
replace (rg_s RG + 96 * Z.of_nat 1 + 4) with (rg_s RG + 100) in V11 by lia.
replace (rg_s RG + 96 * Z.of_nat 2) with (rg_s RG + 192) in V20 by lia.
replace (rg_s RG + 96 * Z.of_nat 2 + 4) with (rg_s RG + 196) in V21 by lia.
replace (rg_s RG + 96 * Z.of_nat 3) with (rg_s RG + 288) in V30 by lia.
replace (rg_s RG + 96 * Z.of_nat 3 + 4) with (rg_s RG + 292) in V31 by lia.
remember (Eimg (Ereg regs1 (dt_dsc_extra f0 o0 f1 o1 f2 o2 f3 o3))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E8 : ew E 8 = Z_to_bv 64 ((rg_s RG + 4) / 8))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 ((rg_s RG + 0) / 8))
  by (rewrite (EREG 9%nat 9%bv) by (first [lia | reflexivity]); rewrite Z.add_0_r; exact R9).
assert (E14 : ew E 14 = Z_to_bv 64 (re_fd e1))
  by (rewrite (EREG 14%nat 14%bv) by (first [lia | reflexivity]); exact R14).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E24 : ew E 24 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat i))
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (E32 : ew E 32 = Z_to_bv 64 f0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 o0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 f1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 o1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 o2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 f3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 o3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (SHOK : sh_ok SEGS BxT SHdsc E (mrestrict (w_H W1) m1)).
{ unfold SHdsc, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_azs_x ly1 S1 W1 m1 md1 E 18 (rg_s RG) 384 HAR);
    [ change 384 with (4 * ASRC); exact HGSZ
    | exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia))
    | exact (U_atom E 18 (rg_s RG) E18 ltac:(lia)) | lia | lia | lia ]. }
assert (HS : st_ok_pi SEGS VAL E (ss_dsc i)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_scan)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_dsc. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                       | intros X; discriminate X |].
    + cbn [sv_denot]. exact R12.
    + cbn [sv_denot]. exact R19.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, dt_dsc_gs.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 32 0) f0);
        [exact (den_atom0 E 32 f0 E32 ltac:(lia)) | zside | zside | rewrite Z.add_0_r; exact V00].
    + apply (chunk_ok_val SEGS E _ _ 4 4 (SOff 33 0) o0);
        [exact (den_atom0 E 33 o0 E33 ltac:(lia)) | zside | zside | exact V01].
    + apply (chunk_ok_val SEGS E _ _ 96 4 (SOff 34 0) f1);
        [exact (den_atom0 E 34 f1 E34 ltac:(lia)) | zside | zside | exact V10].
    + apply (chunk_ok_val SEGS E _ _ 100 4 (SOff 35 0) o1);
        [exact (den_atom0 E 35 o1 E35 ltac:(lia)) | zside | zside | exact V11].
    + apply (chunk_ok_val SEGS E _ _ 192 4 (SOff 36 0) f2);
        [exact (den_atom0 E 36 f2 E36 ltac:(lia)) | zside | zside | exact V20].
    + apply (chunk_ok_val SEGS E _ _ 196 4 (SOff 37 0) o2);
        [exact (den_atom0 E 37 o2 E37 ltac:(lia)) | zside | zside | exact V21].
    + apply (chunk_ok_val SEGS E _ _ 288 4 (SOff 38 0) f3);
        [exact (den_atom0 E 38 f3 E38 ltac:(lia)) | zside | zside | exact V30].
    + apply (chunk_ok_val SEGS E _ _ 292 4 (SOff 39 0) o3);
        [exact (den_atom0 E 39 o3 E39 ltac:(lia)) | zside | zside | exact V31].
  - cbn [pairwise_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [dt_dsc_facts f_atoms atoms_ok]. unfold afact_ok, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite U18, U21. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert HGS1 HGS2 HGS8. clear. unfold SB, SHADOW_OFF. intros.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
destruct i as [|[|[|[|i]]]]; [| | | | lia].
- paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 0 + 4)) HS
    (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 8 (rg_s RG) 4 (Z.of_nat 0) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNR BRR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite ((dt_beqz_sx RG) E 33 o0 E33 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (_ & Ho); lia).
    paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite !wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
    dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
    dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
    dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
    dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC_xR.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
    split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
    split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
    split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
    split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
    split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
    split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
    split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
    split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
    split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split.
    { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      f_equal; cbn [Z.of_nat]; lia. }
    split; [lia|].
    split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 0 + 0)) HS
      (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 9 (rg_s RG) 0 (Z.of_nat 0) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNR BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite ((dt_beq_sx RG HGSB) E 32 14 f0 (re_fd e1) E32 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite ((dt_beqz_sx RG) E 33 o0 E33 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (0 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 0 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo0 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, [], _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)), R18.
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite ((dt_beq_sx RG HGSB) E 32 14 f0 (re_fd e1) E32 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (Hf & _); contradiction).
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
      dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
      dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC_xR.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split.
      { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        f_equal; cbn [Z.of_nat]; lia. }
      split; [lia|].
      split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 1 + 4)) HS
    (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 8 (rg_s RG) 4 (Z.of_nat 1) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNR BRR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite ((dt_beqz_sx RG) E 35 o1 E35 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (_ & Ho); lia).
    paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite !wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
    dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
    dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
    dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
    dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC_xR.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
    split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
    split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
    split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
    split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
    split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
    split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
    split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
    split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
    split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split.
    { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      f_equal; cbn [Z.of_nat]; lia. }
    split; [lia|].
    split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 1 + 0)) HS
      (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 9 (rg_s RG) 0 (Z.of_nat 1) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNR BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite ((dt_beq_sx RG HGSB) E 34 14 f1 (re_fd e1) E34 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite ((dt_beqz_sx RG) E 35 o1 E35 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (1 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 1 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo1 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, [], _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (den_atom E 18 (rg_s RG) 96 E18 ltac:(lia) ltac:(lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite ((dt_beq_sx RG HGSB) E 34 14 f1 (re_fd e1) E34 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (Hf & _); contradiction).
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
      dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
      dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC_xR.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split.
      { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        f_equal; cbn [Z.of_nat]; lia. }
      split; [lia|].
      split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 2 + 4)) HS
    (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 8 (rg_s RG) 4 (Z.of_nat 2) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNR BRR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite ((dt_beqz_sx RG) E 37 o2 E37 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (_ & Ho); lia).
    paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite !wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
    dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
    dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
    dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
    dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC_xR.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
    split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
    split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
    split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
    split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
    split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
    split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
    split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
    split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
    split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
    split.
    { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      f_equal; cbn [Z.of_nat]; lia. }
    split; [lia|].
    split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 2 + 0)) HS
      (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 9 (rg_s RG) 0 (Z.of_nat 2) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNR BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite ((dt_beq_sx RG HGSB) E 36 14 f2 (re_fd e1) E36 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite ((dt_beqz_sx RG) E 37 o2 E37 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (2 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 2 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo2 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, [], _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (den_atom E 18 (rg_s RG) 192 E18 ltac:(lia) ltac:(lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite ((dt_beq_sx RG HGSB) E 36 14 f2 (re_fd e1) E36 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (Hf & _); contradiction).
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
      dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
      dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC_xR.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ (EREG 14%nat 14%bv ltac:(lia) eq_refl)); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split; [rewrite X19; cbn [sv_denot]; unfold w64; f_equal; lia|].
      split.
      { rewrite X24. cbn [sv_denot]. rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        f_equal; cbn [Z.of_nat]; lia. }
      split; [lia|].
      split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  dt_reg HS (11%bv : bv 5) Ra1.
  pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 3 + 4)) HS
    (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 8 (rg_s RG) 4 (Z.of_nat 3) E8 E24 E18 E21 HGS8
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNR BRR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite ((dt_beqz_sx RG) E 39 o3 E39 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (_ & Ho); lia).
    exfalso. lia.
  + paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    dt_reg HS (11%bv : bv 5) Ra1.
    pose proof (dt_reseat E _ _ 11%bv (dt_sh 18 (96 * Z.of_nat 3 + 0)) HS
      (eq_trans Ra1 ((dt_den_add_sh RG HGSB) E 9 (rg_s RG) 0 (Z.of_nat 3) E9 E24 E18 E21 HGS8
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNR HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNR BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite ((dt_beq_sx RG HGSB) E 38 14 f3 (re_fd e1) E38 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite ((dt_beqz_sx RG) E 39 o3 E39 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (3 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 3 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            destruct (Hoo3 Hq) as [Ho|Hf]; [lia | contradiction]).
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite !wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
      dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
      dt_reg HS (13%bv : bv 5) X13. dt_reg HS (18%bv : bv 5) X18. dt_reg HS (21%bv : bv 5) X21.
      dt_reg HS (22%bv : bv 5) X22. dt_reg HS (23%bv : bv 5) X23. dt_reg HS (24%bv : bv 5) X24.
      dt_reg HS (25%bv : bv 5) X25. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, [], _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ (EREG 2%nat 2%bv ltac:(lia) eq_refl)); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ (EREG 3%nat 3%bv ltac:(lia) eq_refl)); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ (EREG 4%nat 4%bv ltac:(lia) eq_refl)); exact R4|].
      split; [rewrite X22, (dt_den_reg E 22 _ (EREG 22%nat 22%bv ltac:(lia) eq_refl)); exact R22|].
      split; [rewrite X25, (dt_den_reg E 25 _ (EREG 25%nat 25%bv ltac:(lia) eq_refl)); exact R25|].
      split; [rewrite X27, (dt_den_reg E 27 _ (EREG 27%nat 27%bv ltac:(lia) eq_refl)); exact R27|].
      split; [rewrite X26, (dt_den_reg E 26 _ (EREG 26%nat 26%bv ltac:(lia) eq_refl)); exact R26|].
      split; [rewrite X18, (dt_den_reg E 18 _ (EREG 18%nat 18%bv ltac:(lia) eq_refl)); exact R18|].
      split; [rewrite X9, (dt_den_reg E 9 _ (EREG 9%nat 9%bv ltac:(lia) eq_refl)); exact R9|].
      split; [rewrite X8, (dt_den_reg E 8 _ (EREG 8%nat 8%bv ltac:(lia) eq_refl)); exact R8|].
      split; [rewrite X21, (dt_den_reg E 21 _ (EREG 21%nat 21%bv ltac:(lia) eq_refl)); exact R21|].
      split.
      { rewrite X23, (den_atom E 18 (rg_s RG) 288 E18 ltac:(lia) ltac:(lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split.
      { rewrite X24, (dt_den_reg E 24 _ (EREG 24%nat 24%bv ltac:(lia) eq_refl)), R24.
        rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ (EREG 10%nat 10%bv ltac:(lia) eq_refl)); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ (EREG 13%nat 13%bv ltac:(lia) eq_refl)); exact R13|].
      split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite ((dt_beq_sx RG HGSB) E 38 14 f3 (re_fd e1) E38 E14 ltac:(lia) ltac:(lia)) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (Hf & _); contradiction).
      exfalso. lia.

Qed.

Lemma dt_DSC_le_xR : forall cx kr sg D i W1 c1, DSC_xR cx kr sg D i W1 c1 -> (i <= dxj cx)%nat.
Proof.
intros cx kr sg D i W1 c1 (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hij & _).
exact Hij.
Qed.

Lemma dt_scan_loop_xR : forall n cx kr sg D i W1 c1,
(4 - i <= n)%nat -> DBASE_x B ARx MT RP MMAX RG cx [] kr -> DSC_xR cx kr sg D i W1 c1 ->
(forall W2 c2, DT2_xR B PST ARx MT RP MMAX RG R cx [] kr sg D W2 c2 ->
   YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
induction n as [|n IH]; intros cx kr sg D i W1 c1 Hn HB HDSC Kf.
- exfalso. pose proof (dt_DSC_le_xR cx kr sg D i W1 c1 HDSC) as Hij.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _). lia.
- apply (dt_scan_step_xR cx kr sg D i W1 c1 HB HDSC); [|exact Kf].
  intros W2 c2 H2. exact (IH cx kr sg D (S i) W2 c2 ltac:(lia) HB H2 Kf).
Qed.

Lemma dt_scan_xR : forall cx kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DT1_xR cx kr sg D W1 c1 ->
(forall W2 c2, DT2_xR B PST ARx MT RP MMAX RG R cx [] kr sg D W2 c2 ->
   YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr sg D W1 c1 HB HDT1 Kf.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDT1 as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & R19 & HMEM & HnoNUL & Hused & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R25 & R27 & R26 & R18 & R9 & R8 & R21 & R23 & R24).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 &
  F224 & F216 & F176 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & Hgarr0 & Hawr0 & HEOK0 & Hj4 & Hsrc0 & Hoth0 & HfdB &
  HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16976 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2.
pose proof HSAME as (Sfd & Seof & Shfd & Shopen & HSrest).
assert (Hfd : hs_fd h1 = re_fd e1) by (rewrite Shfd, HfdB; exact (eq_sym Sfd)).
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (Hfdv : 0 <= re_fd e1 < 2 ^ 31) by (pose proof HEOK as (_ & _ & _ & _ & Hq & _); exact Hq).
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & Hq & _); exact Hq).
(* the relay's table is a live block and g_s an image cell, so the entry and g_s do not overlap (YCbqG.v
   blk_img_x: no block byte is an image byte; HG: g_s is in the image) *)
assert (Hdisj : dxSA cx + 56 <= rg_s RG \/ rg_s RG + 384 <= dxSA cx).
{ destruct (Z_le_gt_dec (dxSA cx + 56) (rg_s RG)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (rg_s RG + 384) (dxSA cx)) as [H2|H2]; [right; exact H2|].
  exfalso.
  assert (Hxg : inG (G_DR B RG) (Z.max (dxSA cx) (rg_s RG)))
    by (unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold ASRC; lia).
  apply (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE (Z.max (dxSA cx) (rg_s RG)) HAR HtblC);
    [rewrite RQT; unfold AENT, ATABLE in *; lia | exact (proj1 (HG _ Hxg))]. }
assert (Hcapb : 0 <= re_cap e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hl & Hq & _); lia).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hbufb : 0 <= re_buf e1 /\ re_buf e1 + re_cap e1 <= alloc_ceiling).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _).
  destruct Hq as [(Hc & Hb & Hu)|(Hc & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hin) as (_ & H4 & Hcl & _).
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq). lia. }
(* the four slots of g_s, as the scan reads them *)
assert (Hslot : forall ii, (ii < 4)%nat -> exists f o,
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii) 4 f /\
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii + 4) 4 o /\
  0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32).
{ intros ii Hii. destruct (Nat.eq_dec ii (dxj cx)) as [->|Hne].
  - pose proof Hsrc as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    unfold dHA, ASRC in V1, V2.
    exists (hs_fd h1), (hs_open h1).
    split; [exact V1|]. split; [exact V2|]. split; [lia|]. rewrite Hopen; lia.
  - assert (HfdvX : 0 <= re_fd (dxe cx) < 2 ^ 31) by (rewrite <- Sfd; exact Hfdv).
    destruct ((dt_others_canon RG HGSB) W1 m1 (dxj cx) (re_fd (dxe cx)) ii Hoth Hii Hne HfdvX)
      as (f & o & V1 & V2 & Bf & Bo & _).
    unfold ASRC in V1, V2. exists f, o. split; [exact V1|]. split; [exact V2|]. split; [exact Bf | exact Bo]. }
destruct (Hslot 0%nat ltac:(lia)) as (f0 & o0 & V00 & V01 & B00 & B01).
destruct (Hslot 1%nat ltac:(lia)) as (f1 & o1 & V10 & V11 & B10 & B11).
destruct (Hslot 2%nat ltac:(lia)) as (f2 & o2 & V20 & V21 & B20 & B21).
destruct (Hslot 3%nat ltac:(lia)) as (f3 & o3 & V30 & V31 & B30 & B31).
replace (rg_s RG + 96 * Z.of_nat 0) with (rg_s RG) in V00 by lia.
replace (rg_s RG + 96 * Z.of_nat 0 + 4) with (rg_s RG + 4) in V01 by lia.
replace (rg_s RG + 96 * Z.of_nat 1) with (rg_s RG + 96) in V10 by lia.
replace (rg_s RG + 96 * Z.of_nat 1 + 4) with (rg_s RG + 100) in V11 by lia.
replace (rg_s RG + 96 * Z.of_nat 2) with (rg_s RG + 192) in V20 by lia.
replace (rg_s RG + 96 * Z.of_nat 2 + 4) with (rg_s RG + 196) in V21 by lia.
replace (rg_s RG + 96 * Z.of_nat 3) with (rg_s RG + 288) in V30 by lia.
replace (rg_s RG + 96 * Z.of_nat 3 + 4) with (rg_s RG + 292) in V31 by lia.
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_sc_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1) (re_fd e1)
  f0 o0 f1 o1 f2 o2 f3 o3))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E18 : ew E 18 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (re_fd e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 f0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 o0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 f1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 o1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 f2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 o2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 10)).
assert (E43 : ew E 43 = Z_to_bv 64 f3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 11)).
assert (E44 : ew E 44 = Z_to_bv 64 o3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 12)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R22).
assert (R25' : getr regs1 25 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R25).
assert (R26' : getr regs1 26 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R26).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R23' : getr regs1 23 = sv_denot E (dt_sh 32 32))
  by (rewrite ((dt_den_sh RG) E 32 (dxSA cx) 32 E32 E21 ltac:(lia) ltac:(lia)); exact R23).
assert (R24' : getr regs1 24 = sv_denot E (dt_sh 32 0))
  by (rewrite ((dt_den_sh RG) E 32 (dxSA cx) 0 E32 E21 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R24).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 0 E18 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R8' : getr regs1 8 = sv_denot E (dt_gv 4))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 4 E18 ltac:(lia) ltac:(lia)); exact R8).
assert (HS : st_ok_pi SEGS VAL E ss_sc
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_mid)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sc. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R19].
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R22' | exact R25' | exact R26' | exact R27' | exact R23' | exact R24'
              | exact R9' | exact R8' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold region_ok, dt_sc_frame, dt_sc_sa, dt_sc_gs, dt_gs_chunks;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 16 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 24 E32 E21 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F224 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 36 0) (re_fd e1));
          [exact (den_atom0 E 36 (re_fd e1) E36 ltac:(lia)) | zside | zside | ].
        rewrite Z.add_0_r. exact ((dt_entry_fd RG HGSB) W1 m1 (dxSA cx) e1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 35 0) (re_buf e1));
          [exact (den_atom0 E 35 (re_buf e1) E35 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_buf RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_used RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_cap RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
    + cbn [base_val]. rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 37 0) f0);
          [exact (den_atom0 E 37 f0 E37 ltac:(lia)) | zside | zside | rewrite Z.add_0_r; exact V00].
      * apply (chunk_ok_val SEGS E _ _ 4 4 (SOff 38 0) o0);
          [exact (den_atom0 E 38 o0 E38 ltac:(lia)) | zside | zside | exact V01].
      * apply (chunk_ok_val SEGS E _ _ 96 4 (SOff 39 0) f1);
          [exact (den_atom0 E 39 f1 E39 ltac:(lia)) | zside | zside | exact V10].
      * apply (chunk_ok_val SEGS E _ _ 100 4 (SOff 40 0) o1);
          [exact (den_atom0 E 40 o1 E40 ltac:(lia)) | zside | zside | exact V11].
      * apply (chunk_ok_val SEGS E _ _ 192 4 (SOff 41 0) f2);
          [exact (den_atom0 E 41 f2 E41 ltac:(lia)) | zside | zside | exact V20].
      * apply (chunk_ok_val SEGS E _ _ 196 4 (SOff 42 0) o2);
          [exact (den_atom0 E 42 o2 E42 ltac:(lia)) | zside | zside | exact V21].
      * apply (chunk_ok_val SEGS E _ _ 288 4 (SOff 43 0) f3);
          [exact (den_atom0 E 43 f3 E43 ltac:(lia)) | zside | zside | exact V30].
      * apply (chunk_ok_val SEGS E _ _ 292 4 (SOff 44 0) o3);
          [exact (den_atom0 E 44 o3 E44 ltac:(lia)) | zside | zside | exact V31].
  - apply pairwise_disjoint_of_extents.
    unfold dt_sc_frame, dt_sc_sa, dt_sc_gs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1 HGS1 HGS2 Hdisj HGle HSAhi. clear.
    unfold DRAIN_FRAME, AENT, ATABLE. intros.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_sc_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U18, U21, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHsc E (mrestrict (w_H W1) m1)).
{ unfold SHsc, sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (dt_shent_sub_x ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
    + exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia)).
    + exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
    + lia.
    + lia.
    + rewrite RQT. unfold AENT, ATABLE in HSAhi. lia.
  - apply (dt_shent_azs_x ly1 S1 W1 m1 md1 E 18 (rg_s RG) 384 HAR);
      [ change 384 with (4 * ASRC); exact HGSZ
      | exact (U_atom E 21 SHADOW_OFF E21 ltac:(unfold SHADOW_OFF; lia))
      | exact (U_atom E 18 (rg_s RG) E18 ltac:(lia)) | lia | lia | lia ]. }
paj_run_to_tok_xR RUNTOR HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
rewrite ?wvb_collapse in HJ.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m1 a)
  by (intros a; exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _)))).
assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ _ HG0 Ha)).
dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (10%bv : bv 5) X10.
dt_reg HS (12%bv : bv 5) X12. dt_reg HS (13%bv : bv 5) X13. dt_reg HS (14%bv : bv 5) X14.
dt_reg HS (18%bv : bv 5) X18. dt_reg HS (19%bv : bv 5) X19. dt_reg HS (21%bv : bv 5) X21.
dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (25%bv : bv 5) X25.
dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
pmkst HS.
apply (dt_scan_loop_xR 4 cx kr sg D 0 _ _ ltac:(lia) HB); [|exact Kf].
unfold DSC_xR.
eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
split; [reflexivity|].
split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
split; [rewrite X25; exact (eq_trans (eq_sym R25') R25)|].
split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
split; [rewrite X26; exact (eq_trans (eq_sym R26') R26)|].
split; [rewrite X18, (dt_den_reg E 18 _ E18); reflexivity|].
split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
split; [rewrite X8; exact (eq_trans (eq_sym R8') R8)|].
split; [rewrite X21, (dt_den_reg E 21 _ E21); reflexivity|].
split; [rewrite X10, ((dt_den_add2 RG HGSB) E 34 35 (re_used e1) (re_buf e1) E34 E35
  ltac:(lia) ltac:(lia) ltac:(lia)); unfold w64; f_equal; lia|].
split; [rewrite X13; exact ((dt_den_room RG HGSB) E (re_cap e1) (re_used e1) E33 E34 ltac:(lia) ltac:(lia))|].
split; [rewrite X14; exact ((dt_den_sx RG) E 36 (re_fd e1) E36 ltac:(lia))|].
split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; lia|].
split; [rewrite X19; cbn [sv_denot]; reflexivity|].
split; [rewrite X24, (dt_den_reg E 21 _ E21); unfold w64; f_equal; cbn [Z.of_nat]; lia|].
split; [lia|].
split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms) md1 _ k1 k1 e1 h1 sg out1 ev1
  (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact HLINK|]. split; [exact HSAME|].
split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
split; [exact Hlater | exact Hbud].
Qed.

(* the top tail at R (W_drain_topb_cx.v Section wR), dr_top_xR's premise *)
Hypothesis dt_tail_xR : dr_toptail_stmt_xR B PST ARx MT RP MMAX RG R.

Theorem dr_top_xR : dr_top_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr s1 D W1 c1 HB HDI Kdi Kend Krb.
assert (EHp : Hp = []) by (destruct HB as ((HAR & _) & _); exact (HP0 _ _ _ _ _ _ HAR)).
subst Hp.
assert (KT2 : forall W2 c2, DT2_xR B PST ARx MT RP MMAX RG R cx [] kr (dgrow s1) D W2 c2 ->
  YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr))
  by (intros W2 c2 H; exact (dt_tail_xR cx [] kr (dgrow s1) D W2 c2 HB H Kdi Kend Krb)).
assert (KT1 : forall W2 c2, DT1_xR cx kr (dgrow s1) D W2 c2 ->
  YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr))
  by (intros W2 c2 H; exact (dt_scan_xR cx kr (dgrow s1) D W2 c2 HB H KT2)).
destruct (Z.le_gt_cases 4096 (drain_b_c.ds_cap s1 - ulen s1)) as [Hge|Hlt].
- exact (dt_nogrow_xR cx kr s1 D W1 c1 HB HDI Hge KT1).
- exact (dt_grow_xR cx kr s1 D W1 c1 HB HDI Hlt KT1).
Qed.

End wR.

(* ---- The three walks that make realloc #1: each is its twin at R := wle, with RO / HA trivial and the strict
   realloc rule lifted to the R rule at wle (W_journal_x.v arealloc_cf_rule_c_xR_of_x). ---- *)
Lemma dt_grow_after_x : forall cx kr s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl c0,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DI_x B PST ARx MT RP MMAX RG cx [] kr s1 D W1 c0 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 8 = w64 ((rg_s RG + 4) / 8) -> getr regs1 9 = w64 (rg_s RG / 8) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 18 = w64 (rg_s RG) -> getr regs1 19 = w64 384 ->
getr regs1 20 = w64 (drain_b_c.ds_cap (dgrow s1)) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 23 = w64 (shadow_addr (dxSA cx + 32)) ->
getr regs1 24 = w64 (shadow_addr (dxSA cx)) -> getr regs1 25 = w64 (dxSA cx + 32) ->
getr regs1 26 = w64 (dxSA cx + 16) -> getr regs1 27 = w64 (dxSA cx + 24) ->
DMEM0 cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud0 cx kr ly1 S1 spent tl ->
(forall W2 c2, DT1_x cx kr (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx [] kr)) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (SIGMA WS_realloc)) m1 (seg_rom SEGS)) md1)
  (dPOST_x B PST ARx MT RP RG cx [] kr).
Proof. exact (dt_grow_after_xR (@wle SEGS) (wle_trans SEGS) (fun _ => True) (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => I)
  (arealloc_cf_rule_c_xR_of_x SEGS B PST ARx MT MMAX RP (fun _ => True) (fun _ _ _ _ _ _ => True) CTX_R (SIGMA WS_realloc) AREALLOC)). Qed.

Lemma dt_grow_x : forall cx kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx [] kr -> DI_x B PST ARx MT RP MMAX RG cx [] kr s1 D W1 c1 ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
(forall W2 c2, DT1_x cx kr (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx [] kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx [] kr).
Proof. exact (dt_grow_xR (@wle SEGS) (wle_trans SEGS) (fun _ => True) (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => I)
  (arealloc_cf_rule_c_xR_of_x SEGS B PST ARx MT MMAX RP (fun _ => True) (fun _ _ _ _ _ _ => True) CTX_R (SIGMA WS_realloc) AREALLOC)). Qed.

(* The TOP TAIL is the frozen statement dr_toptail_stmt_x (W_drain_topb_cx.v Section cx), proved in its own file
   (W_drain_topb.v dr_toptail_x); dr_top_x takes it as a premise. *)
Hypothesis dt_tail_x : dr_toptail_stmt_x B PST ARx MT RP MMAX RG.

Theorem dr_top_x : dr_top_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dr_top_xR (@wle SEGS) (wle_trans SEGS) (fun _ => True) (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => I)
  (arealloc_cf_rule_c_xR_of_x SEGS B PST ARx MT MMAX RP (fun _ => True) (fun _ _ _ _ _ _ => True) CTX_R (SIGMA WS_realloc) AREALLOC) dt_tail_x). Qed.

End cx.
End bx.
End ax.
