(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the GS-FREE arm of segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x83940 .. 0x839b8, gesture_seen's "an END line whose key is held at slot n",
   relay.c:116-119 inlined).  The statement is lib/A/W_drain_gs.v's gs_free_stmt, proved here; the Section
   header below is lib/A/W_drain_cx.v's, verbatim.

   GF (0x83940) -> DLN (S q) (0x836f4), one call and two stores:
     0x83940  lbu a0, 0(s3)   the shadow byte of &s->held[n]; the report arm 0x83d14 is NOT taken
     0x83948  ld  a0, 0(s10)  a0 = s->held[n], the held key's text
     0x8394c  jal free        CALL free #2, through AFREE (afree_cf_rule) on the inner journal
     0x83950  the shadow bytes of &s->held (8(sp)) and &s->nheld (72(sp)); both report arms NOT taken
     0x83974  a3 = s->nheld;  0x83980  sw: s->nheld = nheld - 1
     0x83984  a0 = &s->held[nheld - 1], a1 = &s->held[n], both shadow-checked
     0x839b0  ld; 0x839b4 sd: s->held[n] = s->held[nheld - 1]
     0x839b8  j 0x836f4 = DLN (S q).
   The model step is drain_b_c.seen_tr's GEnd/Some branch: the request RFree (|key| + 1), the held keys
   swap_remove'd at n, the array size unchanged (W_drain_gs.v gs_seen_end_old). *)
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
W_drain_gs W_drain_tr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The symbolic state of the arm at 0x83940. ----
   Atoms 0 .. 31 are the registers (Ereg); the extras are 32 = s->held, 33 = s->nheld,
   34 = s->held + 8 * nheld (one past the last slot), 35 = the last key's address, 36 = the held key's.
   Register 19 (s3) carries the shadow address of &s->held[n], which the search loop computed, so the state
   gives it the shadow EXPRESSION of atom 26 (= &s->held[n]); then the engine's shadow machinery sees every
   one of the arm's four checks in its own form and SH decides all four, with no obligation left.
   Two aliases name the two heap addresses the arm builds out of two atoms each (the PERFORMANCE rule:
   an address built from two atoms gets an alias so `aliased2` collapses it). *)
Definition gf_ceil : Z := 140737479966720.   (* the literal bound of ASAN_CEIL; never the abstract one *)
Definition gf_shA (m : nat) (c : Z) : cval :=
CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0)).
Definition gf_shE (m : nat) (c : Z) : sv :=
SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0).

Definition gf_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 336 0 0
  [ YP09.mkChunk 8 (gf_shA 22 40);
    YP09.mkChunk 72 (gf_shA 22 48);
    YP09.mkChunk 96 (CVal 8 (SOff 22 48));
    YP09.mkChunk 128 (CVal 8 (SOff 22 40)) ].
Definition gf_sa : YP09.region := YP09.mkRegion (Some 22%nat) 40 52 48 52
  [ YP09.mkChunk 40 (CVal 8 (SOff 32 0));
    YP09.mkChunk 48 (CVal 4 (SOff 33 0)) ].
Definition gf_slot : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8
  [ YP09.mkChunk 0 (CVal 8 (SOff 36 0)) ].
Definition gf_last : YP09.region := YP09.mkRegion (Some 34%nat) (-8) 0 0 0
  [ YP09.mkChunk (-8) (CVal 8 (SOff 35 0)) ].

Definition gf_regs : list sv := sr_set sr_atoms 19%bv (gf_shE 26 0).
Definition gf_Bx : sv := SOff 21 0.
Definition gf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* L: the held key is not the last slot, so the last slot is its own region (atom 34 - 8). *)
Definition gf_regionsL : smem := [ gf_frame; gf_sa; gf_slot; gf_last ].
Definition gf_factsL : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0);
  (22%nat, mkAF 4096 gf_ceil 0); (26%nat, mkAF 4096 gf_ceil 3);
  (32%nat, mkAF 4096 gf_ceil 3); (34%nat, mkAF 4096 gf_ceil 3);
  (20%nat, mkAF 0 (2 ^ 29) 3); (33%nat, mkAF 1 (2 ^ 26) 0);
  (35%nat, mkAF 0 gf_ceil 0); (36%nat, mkAF 4096 gf_ceil 0) ] []
  [ (SAlu ALU_ADD (SOff 32 0) (SOff 20 0), SOff 26 0);
    (SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 3)) (SOff 32 0), SOff 34 0) ].
Definition gf_SHL : list shent := [ mkSHE 26 0 8; mkSHE 34 (-8) 0; mkSHE 22 40 52 ].
Definition ss_gfL : sstate := mkSS A_dr_free gf_regs gf_regionsL None gf_factsL.

(* E: the held key IS the last slot (n = nheld - 1).  Then &s->held[nheld - 1] = &s->held[n], the two
   regions of L would coincide and `pairwise_disjoint` would be false, so the state has three regions and
   names s->held + 8 * nheld as atom 26 + 8 instead. *)
Definition gf_regionsE : smem := [ gf_frame; gf_sa; gf_slot ].
Definition gf_factsE : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0);
  (22%nat, mkAF 4096 gf_ceil 0); (26%nat, mkAF 4096 gf_ceil 3);
  (32%nat, mkAF 4096 gf_ceil 3);
  (20%nat, mkAF 0 (2 ^ 29) 3); (33%nat, mkAF 1 (2 ^ 26) 0);
  (36%nat, mkAF 4096 gf_ceil 0) ] []
  [ (SAlu ALU_ADD (SOff 32 0) (SOff 20 0), SOff 26 0);
    (SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 3)) (SOff 32 0), SOff 26 8) ].
Definition gf_SHE : list shent := [ mkSHE 26 0 8; mkSHE 22 40 52 ].
Definition ss_gfE : sstate := mkSS A_dr_free gf_regs gf_regionsE None gf_factsE.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
(* aout_at's three read-only output cells (g_client, g_send_dead, g_send_max) are NOT in G_DR, so neither HG
   nor the free rule's image clause says they are unowned; a call keeps them only through this, which is
   send_line's own header fact (W_send_line_cx.v:86), decidable at the pinned placement. *)
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts *)
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
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

Definition gf_k0 : Z * list byte * list byte := (0, [], []).

(* ---------------------------------------------------------------------------------------------------------
   helpers: byte lists, their lengths, and the garr8 frame
   --------------------------------------------------------------------------------------------------------- *)

Lemma gf_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma gf_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma gf_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.

Lemma gf_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

(* the k-th byte of an n-byte little-endian image of v is le_byte v n k (val_mem's le_byte, YO0f's) *)
Lemma gf_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, gf_nth_zle by exact Hk. rewrite gf_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma gf_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.

Lemma gf_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.

(* a byte run whose ASan view is unchanged keeps its image *)
Lemma gf_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (1) a little-endian field: val_mem from garr8 of its bytes, and back
   --------------------------------------------------------------------------------------------------------- *)

Lemma gf_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite gf_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite gf_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma gf_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite gf_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite gf_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite gf_le_byte1 by exact Hr. reflexivity.
Qed.

Lemma gf_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Lemma gf_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac gf_len := rewrite ?length_app, ?gf_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].
Ltac gf_len_in H := rewrite ?length_app, ?gf_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes in H;
  cbn [length] in H.

(* ---------------------------------------------------------------------------------------------------------
   (2) the two cells of the relay entry that gesture_seen writes
   RelayRep.v:21 entry_bytes e = le4 fd ++ le4 eof ++ le4 skip ++ pad1 ++ le8 buf ++ le8 used ++ le8 cap
                                 ++ le8 hp ++ le4 nheld ++ pad2, so s->held is at + 40 and s->nheld at + 48.
   --------------------------------------------------------------------------------------------------------- */ *)

Lemma gf_entry_hp : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_hp e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 40) 8 (re_hp e).
Proof.
intros W m SA e Hp1 Hhp H.
unfold entry_bytes in H. rewrite !gf_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gf_le8_bytes (re_hp e) Hhp) in H.
apply (gf_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hhp|].
apply (gf_garr8_at _ _ _ _ H). gf_len. lia.
Qed.

Lemma gf_entry_nheld : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_nheld e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 48) 4 (re_nheld e).
Proof.
intros W m SA e Hp1 Hnh H.
unfold entry_bytes in H. rewrite !gf_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gf_le4_bytes (re_nheld e) Hnh) in H.
apply (gf_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hnh|].
apply (gf_garr8_at _ _ _ _ H). gf_len. lia.
Qed.

(* the entry after the two stores: every other byte of the 56 is unchanged *)
Lemma gf_entry_store : forall (W : world SEGS) m (W' : world SEGS) m' SA e e',
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
re_fd e' = re_fd e -> re_eof e' = re_eof e -> re_skip e' = re_skip e -> re_pad1 e' = re_pad1 e ->
re_buf e' = re_buf e -> re_used e' = re_used e -> re_cap e' = re_cap e -> re_pad2 e' = re_pad2 e ->
0 <= re_hp e' < 2 ^ 64 -> 0 <= re_nheld e' < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W' m') (SA + 40) 8 (re_hp e') ->
val_mem SEGS (arm W' m') (SA + 48) 4 (re_nheld e') ->
(forall x, SA <= x < SA + 40 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 52 <= x < SA + 56 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') SA (bzs (entry_bytes e')).

Proof.
intros W m W' m' SA e e' Hp1 Hp2 Efd Eeof Eskip Ep1 Ebuf Eused Ecap Ep2 Hhp Hnh H Vhp Vnh K1 K2.
unfold entry_bytes in H |- *. rewrite Efd, Eeof, Eskip, Ep1, Ebuf, Eused, Ecap, Ep2.
rewrite !gf_bzs_app, !app_assoc in H |- *.
apply garr8_app in H as [H HP2]. apply garr8_app in H as [H _]. apply garr8_app in H as [HZ _].
rewrite (gf_le8_bytes (re_hp e') Hhp), (gf_le4_bytes (re_nheld e') Hnh).
apply garr8_app. split; [apply garr8_app; split; [apply garr8_app; split|]|].
- apply (gf_garr8_kept W m); [exact HZ|]. intros x Hx. apply K1. gf_len_in Hx. lia.
- apply (gf_garr8_at _ (SA + 40)); [|gf_len; lia].
  apply gf_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hhp | exact Vhp].
- apply (gf_garr8_at _ (SA + 48)); [|gf_len; lia].
  apply gf_garr8_of_val; [change (8 * Z.of_nat 4) with 32; exact Hnh | exact Vnh].
- apply (gf_garr8_at _ (SA + 52)); [|gf_len; lia].
  apply (gf_garr8_kept W m).
  + apply (gf_garr8_at _ _ _ _ HP2). gf_len. lia.
  + intros x Hx. apply K2. gf_len_in Hx. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (3) the held array: one 8-byte slot per key (gestures_end_b_c.v:29 key_ptrs)
   --------------------------------------------------------------------------------------------------------- *)

Lemma gf_ptrs_nil : key_ptrs [] = [].
Proof. reflexivity. Qed.

Lemma gf_ptrs_cons : forall k ks, key_ptrs (k :: ks) = Mem.le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs ks.
Proof. reflexivity. Qed.

Lemma gf_ptrs_split : forall a b, key_ptrs (a ++ b) = key_ptrs a ++ key_ptrs b.
Proof. intros a b. unfold key_ptrs. rewrite map_app, concat_app. reflexivity. Qed.

(* the slot of key x, between the slots of the keys before it and after it *)
Lemma gf_ptrs_mid : forall a x b,
key_ptrs (a ++ x :: b) = key_ptrs a ++ Mem.le8 (Z_to_bv 64 (key_addr x)) ++ key_ptrs b.
Proof. intros a x b. rewrite gf_ptrs_split, gf_ptrs_cons. reflexivity. Qed.

(* the slot count, for the array's size bookkeeping *)
Lemma gf_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
rewrite gf_ptrs_cons, length_app, Mem.length_le8, IH. cbn [length]. lia.
Qed.

Lemma gf_nth_last : forall (l : list (Z * list byte * list byte)) z d, nth (length (l ++ [z]) - 1) (l ++ [z]) d = z.
Proof.
intros l z d. rewrite length_app. cbn [length]. replace (length l + 1 - 1)%nat with (length l) by lia. apply nth_middle.
Qed.

Lemma gf_ptrs_slot : forall (W : world SEGS) m hp ks i,
(i < length ks)%nat -> 0 <= key_addr (nth i ks gf_k0) < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W m) (hp + 8 * Z.of_nat i) 8 (key_addr (nth i ks gf_k0)).
Proof.
intros W m hp ks i Hi Hv H.
destruct (nth_split ks gf_k0 Hi) as (l1 & l2 & E & L).
rewrite E, gf_ptrs_mid, !gf_bzs_app in H.
apply garr8_app in H as [_ H]. apply garr8_app in H as [H _].
rewrite (gf_le8_bytes _ Hv) in H.
apply (gf_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (gf_garr8_at _ _ _ _ H). rewrite gf_bzs_len, gf_ptrs_len, L. lia.
Qed.

(* a begin not held: the new key's pointer is appended at slot |ks| *)
Lemma gf_ptrs_app : forall (W : world SEGS) m (W' : world SEGS) m' hp ks k,
0 <= key_addr k < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W' m') (hp + 8 * Z.of_nat (length ks)) 8 (key_addr k) ->
(forall x, hp <= x < hp + 8 * Z.of_nat (length ks) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') hp (bzs (key_ptrs (ks ++ [k]))).
Proof.
intros W m W' m' hp ks k Hk H V K.
rewrite gf_ptrs_split, gf_ptrs_cons, gf_ptrs_nil, app_nil_r, gf_bzs_app.
apply garr8_app. split.
- apply (gf_garr8_kept W m); [exact H|]. intros x Hx. apply K. rewrite gf_bzs_len, gf_ptrs_len in Hx. lia.
- apply (gf_garr8_at _ (hp + 8 * Z.of_nat (length ks))); [|rewrite gf_bzs_len, gf_ptrs_len; lia].
  rewrite (gf_le8_bytes _ Hk). apply gf_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hk | exact V].
Qed.

(* an end held at slot n: the last slot's pointer is written into slot n and the array is one slot shorter *)
Lemma gf_ptrs_swap : forall (W : world SEGS) m (W' : world SEGS) m' hp ks n,
(n < length ks)%nat -> 0 <= key_addr (nth (length ks - 1) ks gf_k0) < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W' m') (hp + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks gf_k0)) ->
(forall x, hp <= x < hp + 8 * Z.of_nat (length ks) ->
   ~ (hp + 8 * Z.of_nat n <= x < hp + 8 * Z.of_nat n + 8) ->
   aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') hp (bzs (key_ptrs (swap_remove gf_k0 n ks))).
Proof.
intros W m W' m' hp ks n Hn Hv H V K.
destruct (nth_split ks gf_k0 Hn) as (a & b & E & L).
set (x := nth n ks gf_k0) in E. clearbody x. subst ks n.
induction b as [|z b' _] using rev_ind.
- (* the held key is the last: the array just loses its last slot *)
  rewrite swap_remove_last.
  rewrite gf_ptrs_split, gf_bzs_app in H. apply garr8_app in H as [H _].
  apply (gf_garr8_kept W m); [exact H|]. intros y Hy. rewrite gf_bzs_len, gf_ptrs_len in Hy.
  apply K; rewrite ?length_app; cbn [length]; lia.
- (* the last key z moves into slot |a| *)
  assert (Ez : nth (length (a ++ x :: b' ++ [z]) - 1) (a ++ x :: b' ++ [z]) gf_k0 = z).
  { replace (a ++ x :: b' ++ [z]) with ((a ++ x :: b') ++ [z]) by (rewrite <- app_assoc; reflexivity).
    apply gf_nth_last. }
  rewrite Ez in Hv, V.
  rewrite swap_remove_mid, gf_ptrs_mid, !gf_bzs_app.
  rewrite gf_ptrs_mid, !gf_bzs_app in H. apply garr8_app in H as [Ha H]. apply garr8_app in H as [_ H].
  rewrite gf_ptrs_split, gf_bzs_app in H. apply garr8_app in H as [Hb _].
  apply garr8_app. split; [|apply garr8_app; split].
  + apply (gf_garr8_kept W m); [exact Ha|]. intros y Hy. rewrite gf_bzs_len, gf_ptrs_len in Hy.
    apply K; rewrite ?length_app; cbn [length]; rewrite ?length_app; cbn [length]; lia.
  + apply (gf_garr8_at _ (hp + 8 * Z.of_nat (length a))); [|rewrite gf_bzs_len, gf_ptrs_len; lia].
    rewrite (gf_le8_bytes _ Hv). apply gf_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hv | exact V].
  + apply (gf_garr8_at _ (hp + 8 * Z.of_nat (length a) + 8)); [|rewrite !gf_bzs_len, gf_ptrs_len, Mem.length_le8; lia].
    apply (gf_garr8_kept W m).
    * apply (gf_garr8_at _ _ _ _ Hb). rewrite !gf_bzs_len, gf_ptrs_len, Mem.length_le8. lia.
    * intros y Hy. rewrite gf_bzs_len, gf_ptrs_len in Hy.
      apply K; rewrite ?length_app; cbn [length]; rewrite ?length_app; cbn [length]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (4) the GS-FREE arm (fuzz_reply.asan 0x83940 .. 0x839b8): free(s->held[n]), s->nheld = nheld - 1,
       s->held[n] = s->held[nheld - 1], over the relay entry's byte image and its invariant
   --------------------------------------------------------------------------------------------------------- *)

(* the entry after the free arm's two stores: only s->nheld changed, and the key list lost slot n *)
Definition gf_entry (e : rentry) (n : nat) : rentry :=
RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e)
   (re_pad2 e) (swap_remove (0, [], []) n (re_keys e)) (re_U e) (re_junk e).

Lemma gf_entry_cnt : forall e n, (n < length (re_keys e))%nat -> re_nheld (gf_entry e n) = re_nheld e - 1.
Proof.
intros e n Hn. unfold re_nheld, gf_entry. cbn [re_keys]. rewrite (gs_swap_remove_len (0, [], []) n (re_keys e) Hn). lia.
Qed.

(* (A) the 56 bytes of the relay entry at SA after the stores *)
Lemma gf_entry_after : forall (W : world SEGS) m (W' : world SEGS) m' SA e n,
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
(n < length (re_keys e))%nat -> 0 <= re_hp e < 2 ^ 64 -> re_nheld e < 2 ^ 26 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W' m') (SA + 48) 4 (re_nheld e - 1) ->
(forall x, SA <= x < SA + 48 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 52 <= x < SA + 56 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') SA (bzs (entry_bytes (gf_entry e n))).
Proof.
intros W m W' m' SA e n Hp1 Hp2 Hn Hhp Hnh H V K1 K2.
pose proof (gf_entry_cnt e n Hn) as E.
assert (Hnh' : 0 <= re_nheld (gf_entry e n) < 2 ^ 32).
{ rewrite E. unfold re_nheld in Hnh |- *. clear - Hn Hnh. lia. }
assert (Vhp : val_mem SEGS (arm W' m') (SA + 40) 8 (re_hp e)).
{ pose proof (gf_entry_hp W m SA e Hp1 Hhp H) as V0.
  apply (gf_val_of_garr8 W' m' (SA + 40) 8 (re_hp e)); [change (8 * Z.of_nat 8) with 64; exact Hhp|].
  apply (gf_garr8_kept W m).
  - apply gf_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hhp | exact V0].
  - intros x Hx. rewrite gf_bzs_len, length_Z_to_le_bytes in Hx. apply K1. clear - Hx. lia. }
rewrite <- E in V.
exact (gf_entry_store W m W' m' SA e (gf_entry e n) Hp1 Hp2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  eq_refl eq_refl Hhp Hnh' H Vhp V (fun x Hx => K1 x ltac:(clear - Hx; lia)) K2).
Qed.

(* (B) the held-key array after the store s->held[n] = s->held[nheld - 1] *)
Lemma gf_array_after : forall (W : world SEGS) m (W' : world SEGS) m' hp ks n,
(n < length ks)%nat -> 0 <= key_addr (nth (length ks - 1) ks (0, [], [])) < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W' m') (hp + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], []))) ->
(forall x, hp <= x < hp + 8 * Z.of_nat (length ks) ->
   ~ (hp + 8 * Z.of_nat n <= x < hp + 8 * Z.of_nat n + 8) ->
   aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') hp (bzs (key_ptrs (swap_remove (0, [], []) n ks))).
Proof.
intros W m W' m' hp ks n Hn Hv H V K. exact (gf_ptrs_swap W m W' m' hp ks n Hn Hv H V K).
Qed.

(* (C) the relay entry's invariant after the free and the two stores *)
Lemma gf_aentry_okx : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e n,
aentry_okx B ly S W m e ->
(n < length (re_keys e))%nat ->
(forall b, In b (aentry_blks (gf_entry e n)) -> In b (ablocks B ly' S')) ->
akept W m W' m'
  ((if re_cap e =? 0 then [] else [gfp (re_buf e) (bzs (re_U e ++ re_junk e))]) ++
   map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (swap_remove (0, [], []) n (re_keys e))) ->
garr8 SEGS (arm W' m') (re_hp e) (bzs (key_ptrs (swap_remove (0, [], []) n (re_keys e)))) ->
aentry_okx B ly' S' W' m' (gf_entry e n).
Proof.
intros ly S W m ly' S' W' m' e n (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14)
  Hn HB HK HA.
assert (HB' : forall b, In b ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
  (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (swap_remove (0, [], []) n (re_keys e))) ->
  In b (ablocks B ly' S')) by exact HB.
clear HB.
pose proof (gf_entry_cnt e n Hn) as E.
pose proof (gs_swap_remove_perm (0, [], []) n (re_keys e) Hn) as P.
unfold aentry_okx. rewrite E. unfold gf_entry.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8
  (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
- (* s->buf *)
  destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; clear - Hc; lia).
  split; [exact Hc|].
  split; [apply HB'; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  rewrite Ec. left. reflexivity.
- (* s->nheld *)
  clear - H10. lia.
- (* s->held *)
  destruct H11 as [(Hz & Hk0) | (Hz & Hin & Hk1 & Hk2 & Hg)].
  + exfalso. rewrite Hk0 in Hn. cbn [length] in Hn. clear - Hn. lia.
  + right. assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
    split; [exact Hz|].
    split; [apply HB'; apply in_or_app; right; rewrite Ez; left; reflexivity|].
    split; [clear - Hk1; lia|].
    split; [exact Hk2 | exact HA].
- (* the key addresses stay distinct *)
  apply NoDup_ListNoDup in H12. apply NoDup_ListNoDup.
  pose proof (Permutation_NoDup (Permutation_map key_addr P) H12) as N.
  cbn [map] in N. apply List.NoDup_cons_iff in N as [_ N]. exact N.
- (* the key texts stay distinct *)
  apply NoDup_ListNoDup in H13. apply NoDup_ListNoDup.
  pose proof (Permutation_NoDup (Permutation_map key_text P) H13) as N.
  cbn [map] in N. apply List.NoDup_cons_iff in N as [_ N]. exact N.
- (* every surviving key *)
  rewrite Forall_forall in H14 |- *. intros k Hk.
  destruct (H14 k (gs_swap_remove_in (0, [], []) n (re_keys e) k Hn Hk)) as (K1 & K2 & K3).
  split; [apply HB'; apply in_or_app; right; apply in_or_app; right;
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
  split; [|exact K3].
  apply (akept_garr8 W m); [|exact K2].
  intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
  apply in_or_app. right.
  apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.
(* (1) the pure set step: removing a held key by swap_remove agrees with the model's upd (filter). *)
Lemma gsf_setswap : forall (H G : list (list Z)) (x : list Z) (n : nat),
NoDup H -> same_set H G -> index_of x H = Some n ->
NoDup (swap_remove [] n H) /\
same_set (swap_remove [] n H) (filter (fun y => negb (list_eqb x y)) G) /\
length (swap_remove [] n H) = (length H - 1)%nat.
Proof.
intros H G x n Hnd Hs E.
apply NoDup_ListNoDup in Hnd.
destruct (index_of_some x H n E) as (a & b & HH & Ha). subst H n.
pose proof (swap_remove_perm [] a x b) as Hp.
assert (Hnd' : List.NoDup (x :: swap_remove [] (length a) (a ++ x :: b)))
  by (eapply Permutation_NoDup; [exact Hp|exact Hnd]).
inversion Hnd' as [|? ? Hx Hnd2]; subst.
split; [apply NoDup_ListNoDup; exact Hnd2|].
split.
- intros y. split.
  + intros Hy. apply list_elem_of_In, list_basics.list.list_elem_of_filter. split.
    * destruct (list_eqb x y) eqn:Exy; [apply list_eqb_true in Exy; subst y; contradiction|exact I].
    * apply list_elem_of_In, (proj1 (Hs y)), (Permutation_in _ (Permutation_sym Hp)). right. exact Hy.
  + intros Hy. apply list_elem_of_In, list_basics.list.list_elem_of_filter in Hy. destruct Hy as [Hn Hy].
    apply list_elem_of_In, (proj2 (Hs y)), (Permutation_in _ Hp) in Hy.
    destruct Hy as [Hy|Hy]; [|exact Hy].
    subst y. rewrite list_eqb_refl in Hn. cbn in Hn. destruct Hn.
- rewrite length_swap_remove, length_app. cbn [length]. lia.
Qed.

(* (2) the line-loop values after the relayed line, for an END whose key is held at slot n. *)
Lemma gsf_line : forall cx s1 (p q jj n : nat),
GSF s1 p q ->
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n ->
drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] /\
drlq s1 p = dline s1 p q :: drlq s1 (S q) /\
dskp s1 (S q) = false /\ dbound s1 (S q) /\ (0 < S q)%nat /\
dlno s1 (S q) = GSno cx s1 p q /\
dloc cx s1 (S q) = GSoc cx s1 p q /\
dlH cx s1 (S q) = swap_remove [] n (dlH cx s1 p) /\
dlka cx s1 (S q) = dlka cx s1 p.
Proof.
intros cx s1 p q jj n HF Hge HI.
unfold GSF in HF. destruct HF as (HB & HPQ & HQ & HNZ & HK & HL).
destruct (gs_drl s1 p q HB HPQ HQ HNZ HK HL) as (E1 & E2 & E3).
destruct (gs_seen_end_old (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ n 0 RelayRunF.adr0 [] Hge HI)
  as (S1 & _ & S3).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
split.
{ unfold dbound. split; [lia|right]. replace (S q - 1)%nat with q by lia. exact HQ. }
split; [lia|].
split; [rewrite (gs_dlno s1 p q E1); unfold GSno; reflexivity|].
split; [rewrite (gs_dloc cx s1 p q E1); unfold GSoc; reflexivity|].
split; [rewrite (gs_dlH cx s1 p q E1); exact S1|].
rewrite (gs_dlka cx s1 p q E1). exact S3.
Qed.

(* (3) the requests: gesture_seen's own request for this arm is a single RFree, and what the cut still owes
   after it is exactly the line loop's remainder from S q. *)
Lemma gsf_fut : forall cx s1 (p q jj n : nat) a jb o ha ks tl,
GSF s1 p q ->
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n ->
GSfut cx s1 p q a jb o ha ks tl ->
exists tl2 jb2,
tl = RelayRunT.RFree (Z.of_nat (length (firstn jj (dline s1 p q))) + 1) (nth n ks RelayRunF.adr0) :: tl2 /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 (S q)) (dloc cx s1 (S q)) (dlH cx s1 (S q))
  (dlka cx s1 (S q)) (drlq s1 (S q)) jb2 o ha (swap_remove RelayRunF.adr0 n ks) tl2.
Proof.
intros cx s1 p q jj n a jb o ha ks tl HF Hge HI HFut.
destruct (gsf_line cx s1 p q jj n HF Hge HI) as (_ & _ & _ & _ & _ & L1 & L2 & L3 & L4).
destruct (gs_seen_end_old (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ n jb ha ks Hge HI) as (S1 & S2 & S3).
unfold GSfut, dsfut in HFut. rewrite S2 in HFut. cbn [fst snd] in HFut.
destruct HFut as (tl2 & Hl & Ht).
rewrite S1, S3 in Hl. rewrite L1, L2, L3, L4.
exists tl2. eexists. split; [exact Ht|exact Hl].
Qed.

(* (4) the history clause after the relayed line. *)
Lemma gsf_hist : forall cx s1 D (p q jj n : nat) h1 LB1 sk1 sk2 H1 ka1 no1 oc1 H2 ka2 no2 oc2,
GSF s1 p q ->
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n ->
H1 = dlH cx s1 p -> ka1 = dlka cx s1 p -> no1 = GSno cx s1 p q -> oc1 = GSoc cx s1 p q -> sk1 = false ->
H2 = dlH cx s1 (S q) -> ka2 = dlka cx s1 (S q) -> no2 = dlno s1 (S q) -> oc2 = dloc cx s1 (S q) ->
sk2 = dskp s1 (S q) ->
DHIST cx (dvirt cx s1 sk1 H1 ka1 no1 oc1) (D ++ ddata s1) (D ++ ddata s1)
  (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p) h1 LB1
  (Z.of_nat (S (length (drlq s1 (S q))))) ->
DHIST cx (dvirt cx s1 sk2 H2 ka2 no2 oc2) (D ++ ddata s1) (D ++ ddata s1)
  (lines (dSTR cx) D ++ drlp s1 (S q)) (lines (dSTR cx) D ++ drlp s1 (S q)) h1 LB1
  (Z.of_nat (length (drlq s1 (S q)))).
Proof.
intros cx s1 D p q jj n h1 LB1 sk1 sk2 H1 ka1 no1 oc1 H2 ka2 no2 oc2 HF Hge HI
  EH1 Eka1 Eno1 Eoc1 Esk1 EH2 Eka2 Eno2 Eoc2 Esk2 HD.
destruct (gsf_line cx s1 p q jj n HF Hge HI) as (E1 & _ & _ & _ & _ & L1 & L2 & L3 & L4).
destruct (gs_index_lt _ _ _ HI) as (Hn & _).
subst H1 ka1 no1 oc1 sk1 H2 ka2 no2 oc2 sk2.
rewrite E1, L1, L2, L3, L4.
unfold DHIST, dvirt, pstream in HD |- *.
cbn [drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_pend drain_b_c.ds_off] in HD |- *.
destruct HD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
destruct (gsf_setswap (dlH cx s1 p) (upds (drain_b_c.keys_texts (re_keys (dxe cx))) (lines (dSTR cx) D ++ drlp s1 p))
  (firstn jj (dline s1 p q)) n D8 D9 HI) as (G1 & G2 & G3).
do 7 (split; [assumption|]).
split; [exact G1|].
split.
{ rewrite app_assoc, gs_upds_snoc. unfold upd. rewrite Hge. cbv beta iota.
  intros y. rewrite (G2 y), <- list_elem_of_In, list_basics.list.list_elem_of_filter, list_elem_of_In, filter_In.
  destruct (negb (list_eqb (firstn jj (dline s1 p q)) y)); cbn [Is_true]; split; intros [Ha Hb];
    first [split; [exact I|exact Ha] | split; [exact Hb|reflexivity] | destruct Ha | discriminate Hb]. }
split; [|exact D11].
rewrite G3. clear - D10 Hn. lia.
Qed.

(* ---- The relay entry's and the held array's addresses as the entry symbolic state names them. ---- *)
Definition gf_key (e : rentry) (n : nat) : Z * list byte * list byte := nth n (re_keys e) gf_k0.
Definition gf_lastkey (e : rentry) : Z * list byte * list byte :=
nth (length (re_keys e) - 1) (re_keys e) gf_k0.
Definition gf_extra (e : rentry) (n : nat) : list word :=
map (Z_to_bv 64)
  [re_hp e; re_nheld e; re_hp e + 8 * re_nheld e; key_addr (gf_lastkey e); key_addr (gf_key e n)].

(* ---- What the arm's run leaves: the free's post and the arm's two stores, in one record. ----
   GFEXC a: the three byte ranges the arm may change, namely the freed key's block, s->nheld and the
   rewritten slot s->held[n].  Everything else the walk reads keeps its view. *)
Definition GFEXC (cx : dcx) (e1 : rentry) (n : nat) (x : Z) : Prop :=
(key_addr (gf_key e1 n) <= x <
   key_addr (gf_key e1 n) + req_size (Z.of_nat (length (key_text (gf_key e1 n))) + 1)) \/
(dxSA cx + 48 <= x < dxSA cx + 52) \/
(re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8).

Definition GFPOST (cx : dcx) (e1 : rentry) (n : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (k1 : Z)
(ly2 : alayout) (S2 : astate) (W2 : world SEGS) (m2 : word -> option byte) (md2 : Model)
(regs1 regs2 : bvmap 5 word) : Prop :=
aregs_preserved regs1 regs2 /\
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 m2 md2 (k1 + 1) /\
frames S2 = frames S1 /\
(exists l1 l2,
   ablocks B ly1 S1 =
     l1 ++ (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: l2 /\
   ablocks B ly2 S2 = l1 ++ l2) /\
mo_le MT S1 S2 (mo_free MT) /\
(forall b m i, In (b, m) (ablocks B ly1 S1) -> 0 <= i < req_size m -> ~ GFEXC cx e1 n (b + i) ->
   aview SEGS (w_H W2) m2 (b + i) = aview SEGS (w_H W1) m1 (b + i)) /\
(forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
   ~ (as_errno B <= x < as_errno B + 4) ->
   aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 ->
   ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 ->
   ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x) /\
apres_kept B W1 m1 W2 m2 /\
(forall i, 0 <= i < 4 ->
   aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) /\
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1 - 1) /\
val_mem SEGS (arm W2 m2) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1)).

(* ---- Auxiliaries of gf_main. ---- *)
Lemma gm_in_zr_dec : forall x r, {in_zr x r} + {~ in_zr x r}.
Proof.
intros x r. unfold in_zr. destruct (Z_le_gt_dec (fst r) x); destruct (Z_lt_ge_dec x (fst r + snd r));
[left; lia | right; lia | right; lia | right; lia].
Qed.

Lemma gm_bk_trans : forall (W0 : world SEGS) m0 (W1 : world SEGS) m1 (W2 : world SEGS) m2 x,
abyte_kept W0 m0 W1 m1 x -> abyte_kept W1 m1 W2 m2 x -> abyte_kept W0 m0 W2 m2 x.
Proof.
intros W0 m0 W1 m1 W2 m2 x [V1 P1] [V2 P2]. split; [rewrite V2; exact V1 | intros H; exact (P2 (P1 H))].
Qed.

(* a byte stays writable across two worlds when its presence is kept *)
Lemma gm_writable_kept : forall (H H2 : word -> bool) (m m2 : word -> option byte) a,
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
Lemma gm_img_wr : forall (W : world SEGS) m a,
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
Lemma gm_sep_head : forall ly S (W : world SEGS) m md x L y,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

(* the relay entry's blocks lose the freed key's block *)
Lemma gm_perm_entry : forall e n, (n < length (re_keys e))%nat ->
Permutation (aentry_blks e)
  ((key_addr (gf_key e n), Z.of_nat (length (key_text (gf_key e n))) + 1) :: aentry_blks (gf_entry e n)).
Proof.
intros e n Hn. unfold aentry_blks, gf_entry, gf_key, gf_k0. cbn [re_cap re_buf re_hp re_kh re_keys].
pose proof (Permutation_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))
  (gs_swap_remove_perm (0, [], []) n (re_keys e) Hn)) as P. cbn [map] in P.
rewrite !app_assoc. eapply Permutation_trans; [apply Permutation_app_head; exact P|].
apply Permutation_sym, Permutation_middle.
Qed.

Lemma gm_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.

(* every byte a list's predicate reads is in its struct or in one of its blocks *)
Lemma gm_list_fp : forall ly S (W : world SEGS) m LA l lines, alist_at B ly S W m LA l lines ->
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
  unfold bzs in Hx. rewrite length_map, length_app, gm_concat_len in Hx. unfold req_size, AREC, hl_n in *.
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
Lemma gm_src_fp : forall ly S (W : world SEGS) m HA h, asrc_at B ly S W m HA h ->
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
  + destruct (gm_list_fp ly S W m (HA + 16) (hs_pending h) false Hpend r x Hr Hx) as [H | (b & Hb & Hbx)];
      [left; unfold ASRC; lia | right; exists b; split; [right; apply in_or_app; left; exact Hb | exact Hbx]].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (gm_list_fp ly S W m (HA + 64) (hs_expected h) true Hexp r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hbx]].
    * destruct (gm_list_fp ly S W m (HA + 80) (hs_held h) true Hheld r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbx]].
Qed.

(* every byte the output's predicate reads is a walk global, one of its three read-only cells, or g_out *)
Lemma gm_out_fp : forall cap out r x, In r (aout_fp B RG cap out) -> fst r <= x < snd r ->
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
Lemma gm_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
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

(* the line loop's registers and frame slots, across two worlds *)
Lemma gm_dregs_kept : forall cx regs regs' (W : world SEGS) m (W' : world SEGS) m',
dregs_line RG cx regs W m ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 22 = getr regs 22 -> getr regs' 27 = getr regs 27 -> getr regs' 18 = getr regs 18 ->
getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 -> getr regs' 21 = getr regs 21 ->
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dregs_line RG cx regs' W' m'.
Proof.
intros cx regs regs' W m W' m' HR E2 E3 E4 E22 E27 E18 E9 E8 E21 KF.
destruct HR as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
unfold dregs_line. unfold spZ in *. rewrite E2, E3, E4, E22, E27, E18, E9, E8, E21.
do 9 (split; [assumption|]).
split; [exact (gm_frame_kept cx W m W' m' KF HFR)|].
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
apply V; [lia | lia | assumption].
Qed.

(* the trace meters of a free *)
Lemma gm_tr_free : forall sz x (t : dtrace),
tr_cost MT (RelayRunT.RFree sz x :: t) = mo_free MT + tr_cost MT t /\
tr_alloc (RelayRunT.RFree sz x :: t) = tr_alloc t /\ tr_max (RelayRunT.RFree sz x :: t) = tr_max t.
Proof.
intros sz x t. split; [reflexivity|]. split; [|reflexivity].
unfold tr_alloc. cbn [fold_right]. lia.
Qed.

(* C3: the key at slot n of the held keys has the length the model's held text at slot n has, so the free's block is
   exactly the trace's RFree (|key| + 1) *)
Lemma gf_keylen : forall (ks : list (Z * list byte * list byte)) n (x : list Z),
  (n < length ks)%nat -> nth n (drain_b_c.keys_texts ks) [] = x ->
  Z.of_nat (length (key_text (nth n ks gf_k0))) = Z.of_nat (length x).
Proof.
unfold drain_b_c.keys_texts.
induction ks as [|k ks IH]; intros [|n] x Hn Hx; cbn [length] in Hn; [lia | lia | |].
- cbn [map nth] in Hx |- *. subst x. unfold bzs. rewrite length_map. reflexivity.
- cbn [map nth] in Hx |- *. apply IH; [lia | exact Hx].
Qed.

Ltac gm_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

(* The cut the arm lands on, from the arm's post: everything that is not the symbolic run. *)
Lemma gf_main : forall cx s1 D p q regs1 ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent
  jb a o ha ks tl jj n ly2 S2 (W2 : world SEGS) m2 md2 regs2,
DBASE B MT MMAX RG cx ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
(n < length (re_keys e1))%nat ->
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) ->
(13 < jj < q - p)%nat ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n ->
GSF s1 p q ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
GSfut cx s1 p q a jb o ha ks tl ->
GFPOST cx e1 n ly1 S1 W1 m1 k1 ly2 S2 W2 m2 md2 regs1 regs2 ->
DLN B MT MMAX RG cx s1 D (S q) W2 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2).
Proof.
intros cx s1 D p q regs1 ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl jj n ly2 S2 W2 m2 md2 regs2
  HB HRL R23 Hn Hge Hjj HI HF HCORE HFUT HPOST.
destruct HPOST as (HPR & HJ2 & HFR2 & (l1 & l2 & EB1 & EB2) & HMO & HKB & HKI & HKS & HPS & HAPK & HKE & VNH & VSL).
destruct HCORE as (HDMEM & HLINK & HSAME & HHIST & HRST & HBUD).
destruct HDMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT & HLIVE & HPERM).
cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no] in HOUT, HPERM, HLIVE.
destruct (gsf_line cx s1 p q jj n HF Hge HI) as (LP & _ & LSK & LBD & LPOS & LNO & LOC & LH & LKA).
destruct (gsf_fut cx s1 p q jj n a jb o ha ks tl HF Hge HI HFUT) as (tl2 & jb2 & Etl & HFUT2).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
assert (AR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (AR2 : AR SEGS B ly2 S2 W2 m2 md2) by (eapply ajournal_gx_AR; exact HJ2).
pose proof HOKX as (_ & _ & Hp1 & Hp2 & _ & _ & HU & _ & _ & Hnh & HHP & _ & _ & HKEYS).
destruct HHP as [(Hz & Hk0) | (Hz & HinH & Hk1 & Hk2 & HgA)];
  [exfalso; rewrite Hk0 in Hn; cbn [length] in Hn; clear - Hn; lia|].
assert (Ez : (re_hp e1 =? 0) = false) by (apply Z.eqb_neq; exact Hz).
assert (RQH : req_size (re_kh e1) = re_kh e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0) as [E0|E0]; [exfalso; clear - Hk2 E0; lia | reflexivity]).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (HSLOT : re_hp e1 + 8 * Z.of_nat n + 8 <= re_hp e1 + re_kh e1)
  by (unfold re_nheld in Hk1; clear - Hk1 Hn; lia).
assert (HHP64 : 0 <= re_hp e1 < 2 ^ 64).
{ destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ AR1 HinH) as (_ & H4 & Hc & _). rewrite RQH in Hc.
  clear - H4 Hc HAC Hk2. lia. }
(* ---- the live blocks before and after the free ---- *)
match type of HPERM with Permutation _ (_ :: aentry_blks _ ++ ?r) => pose (R := r) end.
pose (TB := (dxG cx, ATABLE)).
pose (HBk := (re_hp e1, re_kh e1)).
pose (BUF := if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]).
pose (KEYS2 := map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (swap_remove (0, [], []) n (re_keys e1))).
pose (X := BUF ++ KEYS2 ++ R).
assert (EA2 : aentry_blks (gf_entry e1 n) = BUF ++ HBk :: KEYS2).
{ unfold aentry_blks, gf_entry. cbn [re_cap re_buf re_hp re_kh re_keys]. rewrite Ez. reflexivity. }
assert (P1 : Permutation (ablocks B ly1 S1)
  ((key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: TB :: aentry_blks (gf_entry e1 n) ++ R)).
{ eapply Permutation_trans; [exact HPERM|].
  eapply Permutation_trans; [apply perm_skip; apply Permutation_app_tail; exact (gm_perm_entry e1 n Hn)|].
  cbn [app]. apply perm_swap. }
assert (P2 : Permutation (ablocks B ly2 S2) (TB :: aentry_blks (gf_entry e1 n) ++ R)).
{ rewrite EB2.
  apply (Permutation_cons_inv (a := (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- EB1. exact P1. }
assert (PT : Permutation (ablocks B ly2 S2) (TB :: HBk :: X)).
{ eapply Permutation_trans; [exact P2|]. apply perm_skip. rewrite EA2, <- app_assoc. cbn [app].
  apply Permutation_sym, Permutation_middle. }
assert (PH : Permutation (ablocks B ly2 S2) (HBk :: TB :: X)) by exact (Permutation_trans PT (perm_swap HBk TB X)).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PT)); left; reflexivity).
assert (HB2 : In HBk (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PH)); left; reflexivity).
assert (X2 : forall b, In b X -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym PT)); right; right; exact Hb).
assert (SUB : forall b, In b (ablocks B ly2 S2) -> In b (ablocks B ly1 S1) /\
  zdisjoint (block_rng (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1)) (block_rng b)).
{ intros b Hb. rewrite EB2 in Hb. split.
  - rewrite EB1. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb].
  - apply (gm_sep_head ly1 S1 W1 m1 md1 _ (l1 ++ l2));
      [exact AR1 | rewrite EB1; apply Permutation_sym, Permutation_middle | exact Hb]. }
assert (DTH : zdisjoint (block_rng TB) (block_rng HBk))
  by exact (gm_sep_head ly2 S2 W2 m2 md2 TB (HBk :: X) HBk AR2 PT (or_introl eq_refl)).
assert (DTX : forall b, In b X -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (gm_sep_head ly2 S2 W2 m2 md2 TB (HBk :: X) b AR2 PT (or_intror Hb))).
assert (DHX : forall b, In b X -> zdisjoint (block_rng HBk) (block_rng b))
  by (intros b Hb; exact (gm_sep_head ly2 S2 W2 m2 md2 HBk (TB :: X) b AR2 PH (or_intror Hb))).
(* ---- what the arm keeps ---- *)
assert (VK : forall b x, In b (ablocks B ly2 S2) -> fst b <= x < fst b + req_size (snd b) ->
  ~ (dxSA cx + 48 <= x < dxSA cx + 52) -> ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros [pb mb] x Hb Hx H48 Hsl. destruct (SUB _ Hb) as (Hb1 & Hd). cbn [fst snd] in Hx.
  assert (Hi : 0 <= x - pb < req_size mb) by (clear - Hx; lia).
  pose proof (HKB pb mb (x - pb) Hb1 Hi) as E. replace (pb + (x - pb)) with x in E by ring.
  apply E. unfold GFEXC. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  intros [G1 | [G2 | G3]]; [clear - G1 Hd Hx; lia | exact (H48 G2) | exact (Hsl G3)]. }
assert (WK : forall b x, In b (ablocks B ly2 S2) -> fst b <= x < fst b + req_size (snd b) ->
  writable_at SEGS (arm W2 m2) x).
{ intros [pb mb] x Hb Hx. destruct (al_blocks SEGS B LAWS ly2 S2 W2 m2 md2 pb mb AR2 Hb) as (_ & _ & _ & _ & Hpr & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (BK : forall b x, In b (ablocks B ly2 S2) -> fst b <= x < fst b + req_size (snd b) ->
  ~ (dxSA cx + 48 <= x < dxSA cx + 52) -> ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8) ->
  abyte_kept W1 m1 W2 m2 x).
{ intros b x Hb Hx H48 Hsl. split; [exact (VK b x Hb Hx H48 Hsl) | intros _; exact (WK b x Hb Hx)]. }
assert (KO : forall b x, In b X -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 x).
{ intros b x Hb Hx. apply (BK b x (X2 b Hb) Hx).
  - intros H48. pose proof (DTX b Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj. rewrite RQT in Dj.
    clear - Dj Hx H48 HGle HSAle. unfold AENT, ATABLE in *. lia.
  - intros Hs. pose proof (DHX b Hb) as Dj. unfold zdisjoint, block_rng, HBk in Dj. cbn [fst snd] in Dj. rewrite RQH in Dj.
    clear - Dj Hx Hs HSLOT. lia. }
assert (TK : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (dxSA cx + 48 <= x < dxSA cx + 52) ->
  abyte_kept W1 m1 W2 m2 x).
{ intros x Hx H48. apply (BK TB x TB2); [| exact H48 |].
  - unfold TB. cbn [fst snd]. rewrite RQT. clear - Hx HGle HSAle. unfold AENT, ATABLE in *. lia.
  - intros Hs. pose proof DTH as Dj. unfold zdisjoint, block_rng, TB, HBk in Dj. cbn [fst snd] in Dj. rewrite RQT, RQH in Dj.
    clear - Dj Hx Hs HSLOT HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (HK : forall x, re_hp e1 <= x < re_hp e1 + re_kh e1 ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8) -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx Hs. apply (BK HBk x HB2); [| | exact Hs].
  - unfold HBk. cbn [fst snd]. rewrite RQH. exact Hx.
  - intros H48. pose proof DTH as Dj. unfold zdisjoint, block_rng, TB, HBk in Dj. cbn [fst snd] in Dj. rewrite RQT, RQH in Dj.
    clear - Dj Hx H48 HGle HSAle. unfold AENT, ATABLE in *. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (EV : aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
  { replace x with (as_errno B + (x - as_errno B)) by ring. apply HKE. clear - Hx; lia. }
  split; [exact EV|]. intros _.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  apply gm_img_wr; [exact (proj1 (HG x Hg)) | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [exact (conj (proj1 (HG x Hx)) (proj1 (proj2 (HG x Hx)))) | exact (conj (proj1 (HGO x Hx)) (proj1 (proj2 (HGO x Hx))))]).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by lia.
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  split; [exact (HKI x Hi Ho Hne)|].
  intros Hw. apply (gm_writable_kept (w_H W1) (w_H W2) m1 m2 x); [|exact Hw].
  intros Hp. exact (HAPK x Hi Ho Hne Hp). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
assert (FB : alloc_ceiling + DRAIN_STK <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
assert (FK2 : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (Hr : alloc_ceiling <= x < 2 ^ 64 /\ ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME))
    by (clear - Hx FB; unfold DRAIN_STK, SL_STK, SL_FRAME, DRAIN_FRAME, ASTACK in *; lia).
  destruct Hr as [Hr1 Hr2].
  split; [exact (HKS x Hr1 Hr2)|]. intros Hw. apply (gm_writable_kept (w_H W1) (w_H W2) m1 m2 x); [|exact Hw].
  exact (HPS x Hr1 Hr2). }
(* ---- the registers ---- *)
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
{ intros r Hr. pose proof (HPR (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
assert (DR2 : dregs_line RG cx regs2 W2 m2).
{ apply (gm_dregs_kept cx regs1 regs2 W1 m1 W2 m2 HRL); try (apply PR; gm_cs). exact FK2. }
assert (E23 : getr regs2 23 = getr regs1 23) by (apply PR; gm_cs).
(* ---- the memory core ---- *)
assert (ROM2 : rom_view SEGS W2 m2).
{ intros x Hx. destruct (HROMO x Hx) as (_ & Hpin & Hne & _).
  destruct (Exists_dec (in_zr x) (as_owned_static B) (gm_in_zr_dec x)) as [Hown | Hno].
  - eapply rom_pinned_view; [exact AR2 | exact (Hpin Hown)].
  - assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    rewrite (HKI x Hi Hno Hne). exact (HROM x Hx). }
assert (PK2 : apres_kept B (dxW cx) (dxmem cx) W2 m2)
  by (intros x Hi Ho He Hp; exact (HAPK x Hi Ho He (HPRESK x Hi Ho He Hp))).
assert (ENT2 : garr8 SEGS (arm W2 m2) (dxSA cx) (bzs (entry_bytes (gf_entry e1 n)))).
{ apply (gf_entry_after W1 m1 W2 m2 (dxSA cx) e1 n Hp1 Hp2 Hn HHP64 Hnh HENTB VNH).
  - intros x Hx. exact (proj1 (TK x ltac:(clear - Hx; unfold AENT; lia) ltac:(clear - Hx; lia))).
  - intros x Hx. exact (proj1 (TK x ltac:(clear - Hx; unfold AENT; lia) ltac:(clear - Hx; lia))). }
assert (AWR2 : awr W2 m2 (dxSA cx) AENT).
{ intros i Hi. apply (WK TB (dxSA cx + i) TB2). unfold TB. cbn [fst snd]. rewrite RQT.
  clear - Hi HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (OKX2 : aentry_okx B ly2 S2 W2 m2 (gf_entry e1 n)).
{ apply (gf_aentry_okx ly1 S1 W1 m1 ly2 S2 W2 m2 e1 n HOKX Hn).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym P2)). right. apply in_or_app. left. exact Hb.
  - intros r Hr x Hx. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    + destruct (re_cap e1 =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
      pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & HBUF & _).
      destruct HBUF as [(Hc0 & _) | (Hcp & _ & HJk & _)]; [apply Z.eqb_neq in Ec; contradiction|].
      apply (KO (re_buf e1, re_cap e1) x).
      * apply in_or_app. left. unfold BUF. rewrite ?Ec. left. reflexivity.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        pose proof (req_size_pos (re_cap e1) ltac:(clear - Hcp; lia)) as (_ & RQ). clear - Hx HU HJk RQ. lia.
    + apply in_map_iff in Hr as (k & <- & Hk).
      apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
      * apply in_or_app. right. apply in_or_app. left. unfold KEYS2.
        apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        cbn [length] in Hx.
        pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & RQ). clear - Hx RQ. lia.
  - apply (gf_array_after W1 m1 W2 m2 (re_hp e1) (re_keys e1) n Hn); [| exact HgA | exact VSL |].
    + assert (Hin : In (nth (length (re_keys e1) - 1) (re_keys e1) (0, [], [])) (re_keys e1))
        by (apply nth_In; clear - Hn; lia).
      rewrite Forall_forall in HKEYS. destruct (HKEYS _ Hin) as (Hb & _).
      destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ AR1 Hb) as (_ & H4 & Hc & _).
      pose proof (req_size_pos (Z.of_nat (length (key_text (nth (length (re_keys e1) - 1) (re_keys e1) (0, [], [])))) + 1)
        ltac:(lia)) as (_ & RQ).
      clear - H4 Hc HAC RQ. lia.
    + intros x Hx Hs. exact (proj1 (HK x ltac:(unfold re_nheld in Hk1; clear - Hx Hk1; lia) Hs)). }
assert (SRC2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. destruct (gm_src_fp ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. apply in_or_app. right. apply in_or_app. right. unfold R. apply in_or_app. left.
      exact Hb.
  - intros b Hb. apply X2. apply in_or_app. right. apply in_or_app. right. unfold R. apply in_or_app. left. exact Hb. }
assert (OTH2 : aothers_at RG W2 m2 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & V1 & V2 & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m2) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact V1] | split; [apply GV; [| | exact V2] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK2 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m2 x)
  by (intros x H1 H2; exact (gm_bk_trans _ _ W1 m1 W2 m2 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT2 : aout_at B RG ly2 S2 W2 m2 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct (gm_out_fp _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, GSoc cx s1 p q) x).
    + apply in_or_app. right. apply in_or_app. right. unfold R. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply X2. apply in_or_app. right. apply in_or_app. right. unfold R. apply in_or_app. right.
    apply in_or_app. left. exact Hb. }
assert (DM2 : DMEM B RG cx ly2 S2 W2 m2 md2 (k1 + 1) (gf_entry e1 n) h1
  (dvirt cx s1 false (swap_remove [] n (dlH cx s1 p)) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))
  out1 ev1 (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) LB1).
{ unfold DMEM. cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no].
  refine (conj HJ2 (conj ROM2 (conj PK2 (conj (eq_trans HFR2 HFRM) (conj (gm_frame_kept cx W1 m1 W2 m2 FK2 HFRAME)
    (conj ENT2 (conj AWR2 (conj OKX2 (conj SRC2 (conj OTH2 (conj GSK2 (conj OUT2 (conj HLIVE _))))))))))))).
  exact P2. }
(* ---- the model ---- *)
assert (DL2 : DLINK (dvirt cx s1 false (swap_remove [] n (dlH cx s1 p)) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))
  (gf_entry e1 n) h1).
{ pose proof HLINK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  refine (conj K1 (conj K2 (conj K3 (conj _ (conj K5 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10 (conj K11 K12))))))))))).
  cbn [gf_entry re_keys dvirt drain_b_c.ds_H]. rewrite (gs_keys_texts_swap (re_keys e1) n Hn). f_equal. exact K4. }
pose proof (gsf_hist cx s1 D p q jj n h1 LB1 false false (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q)
  (swap_remove [] n (dlH cx s1 p)) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q) HF Hge HI
  eq_refl eq_refl eq_refl eq_refl eq_refl (eq_sym LH) (eq_sym LKA) (eq_sym LNO) (eq_sym LOC) (eq_sym LSK) HHIST) as DH2.
rewrite LP in DH2.
assert (DB2 : dbud MT MMAX cx S2 (spent + mo_free MT) tl2).
{ pose proof HBUD as (Hle & Hsp & Hcost & Hlv & Hmax). rewrite Etl in Hcost, Hlv, Hmax.
  rewrite (proj1 (gm_tr_free _ _ _)) in Hcost. rewrite W_tr_peak.tr_peak_free in Hlv.
  rewrite (proj2 (proj2 (gm_tr_free _ _ _))) in Hmax.
  pose proof (mo_free_nonneg MT MTL) as Hf0.
  (* C3: the free lowers the live bytes by exactly the key's block, the trace's RFree (|key| + 1), so the peak of the
     rest stays in room (W_tr_peak.v tr_peak_free) *)
  assert (HKL : Z.of_nat (length (key_text (gf_key e1 n))) = Z.of_nat (length (firstn jj (dline s1 p q)))).
  { pose proof HLINK as (_ & _ & _ & K4 & _). cbn [dvirt drain_b_c.ds_H] in K4.
    destruct (gs_index_lt _ _ _ HI) as (_ & Hnth). rewrite <- K4 in Hnth.
    exact (gf_keylen (re_keys e1) n _ Hn Hnth). }
  assert (BB : blocks_bytes S2 = blocks_bytes S1 - (Z.of_nat (length (key_text (gf_key e1 n))) + 1)).
  { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), EB1, EB2, !bsum_app, bsum_cons. cbn [snd]. lia. }
  split; [exact (mle_station MT (dxS cx) S1 S2 spent (mo_free MT) MTL Hle HMO)|].
  split; [lia|]. split; [lia|]. split; [lia | exact Hmax]. }
(* ---- the cut ---- *)
unfold DLN.
exists regs2, ly2, S2, m2, md2, (k1 + 1), (gf_entry e1 n), h1, out1, ev1, LB1, (spent + mo_free MT), jb2, a, o, ha,
  (swap_remove RelayRunF.adr0 n ks), tl2.
split; [reflexivity|].
split; [exact DR2|].
split; [cbn [gf_entry re_buf]; rewrite E23, R23; unfold w64; f_equal; lia|].
split; [exact LBD|].
split; [exact LPOS|].
split; [|exact HFUT2].
unfold DLC, LCORE. cbv zeta.
rewrite LP, LSK, LNO, LOC, LH, LKA.
exact (conj DM2 (conj DL2 (conj HSAME (conj DH2 (conj HRST DB2))))).
Qed.

(* =========================================================================================================
   The run's own lemmas.
   ========================================================================================================= *)

(* the shadow-address arithmetic over atom 21 (W_drain_feed.v's df_U_srl / df_U_shadow) *)
Lemma gfr_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma gfr_U_sh : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (gf_shE n c) = (v + c) / 8 + SHADOW_OFF.
Proof.
intros E n v c Hn H21 Hv Hc. unfold gf_shE. rewrite U_SAlu. cbn [zalu_raw].
rewrite (gfr_U_srl E n v c Hn Hv Hc), (U_atom E 21 SHADOW_OFF H21) by (unfold SHADOW_OFF; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma gfr_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma gfr_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma gfr_den_eq : forall E a b, U E a = U E b -> sv_denot E a = sv_denot E b.
Proof. intros E a b H. unfold U in H. apply bv_eq. exact H. Qed.

Lemma gfr_U_add : forall E x y, 0 <= U E x + U E y < 2 ^ 64 -> U E (SAlu ALU_ADD x y) = U E x + U E y.
Proof. intros E x y H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.

Lemma gfr_U_sll3 : forall E x, 0 <= U E x -> 8 * U E x < 2 ^ 64 -> U E (SAlu ALU_SLL x (SLit 3)) = 8 * U E x.
Proof.
intros E x H0 H1. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* a block pair of a live state occurs at most once in it *)
Lemma gfr_dup : forall ly S (W : world SEGS) mem md x l1 l2 l3,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ x :: l2 ++ x :: l3) -> 0 <= snd x -> False.
Proof.
intros ly S W mem md x l1 l2 l3 HAR HP Hx.
assert (HP2 : Permutation (l1 ++ x :: l2 ++ x :: l3) (x :: x :: (l1 ++ l2) ++ l3)).
{ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite app_assoc. apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x x _ HAR (Permutation_trans HP HP2)) as D.
destruct x as [b m]. unfold zdisjoint, block_rng in D. cbn [fst snd] in D, Hx.
pose proof (req_size_pos m Hx). lia.
Qed.

Lemma gfr_dup_in : forall ly S (W : world SEGS) mem md L1 L2 x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ x :: L2) -> In x L2 -> 0 <= snd x -> False.
Proof.
intros ly S W mem md L1 L2 x HAR HP Hin Hx. apply in_split in Hin as (l2 & l3 & ->).
exact (gfr_dup ly S W mem md x L1 l2 l3 HAR HP Hx).
Qed.

(* one shadow entry over a sub-range of a live block *)
Lemma gfr_shent : forall Ex ly S (W : world SEGS) mem md b m (mt : nat) p lo hi,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> U Ex gf_Bx = SHADOW_OFF -> U Ex (SOff mt 0) = p ->
b <= p + lo -> lo <= hi -> p + hi <= b + req_size m ->
shent_ok SEGS gf_Bx Ex (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros Ex ly S W mem md b m mt p lo hi HAR Hin HBx Hp H1 H2 H3.
pose proof asan_consts as (C1 & _).
destruct (al_blocks SEGS B LAWS ly S W mem md b m HAR Hin) as (_ & H4 & Hc & Happ & _).
eapply shent_ok_of_range.
- exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m (p + lo) (hi - lo) HAR Hin H1 ltac:(lia)).
- exact HBx.
- exact Hp.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.

(* ---- The entry state, variant L (the held key is not the last slot). ---- *)
Lemma gfr_entryL : forall (W : world SEGS) regs mem sp SA hp nh n kl kn,
spZ regs = sp -> alloc_ceiling + 16512 <= sp -> sp + 336 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 21 = w64 SHADOW_OFF -> getr regs 22 = w64 SA -> getr regs 20 = w64 (8 * n) ->
getr regs 26 = w64 (hp + 8 * n) -> getr regs 19 = w64 ((hp + 8 * n) / 8 + SHADOW_OFF) ->
4096 <= SA -> SA + 56 <= alloc_ceiling ->
4096 <= hp -> hp mod 8 = 0 -> 0 <= n -> n + 1 < nh -> nh < 2 ^ 26 -> hp + 8 * nh <= alloc_ceiling ->
(SA + 52 <= hp \/ hp + 8 * nh <= SA + 40) ->
4096 <= kn <= alloc_ceiling -> 0 <= kl <= alloc_ceiling ->
val_mem SEGS (arm W mem) (sp + 8) 8 ((SA + 40) / 8 + SHADOW_OFF) ->
val_mem SEGS (arm W mem) (sp + 72) 8 ((SA + 48) / 8 + SHADOW_OFF) ->
val_mem SEGS (arm W mem) (sp + 96) 8 (SA + 48) ->
val_mem SEGS (arm W mem) (sp + 128) 8 (SA + 40) ->
val_mem SEGS (arm W mem) (SA + 40) 8 hp ->
val_mem SEGS (arm W mem) (SA + 48) 4 nh ->
val_mem SEGS (arm W mem) (hp + 8 * n) 8 kn ->
val_mem SEGS (arm W mem) (hp + 8 * nh - 8) 8 kl ->
(forall o, 48 <= o < 52 -> writable_at SEGS (arm W mem) (SA + o)) ->
(forall o, 0 <= o < 8 -> writable_at SEGS (arm W mem) (hp + 8 * n + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) [hp; nh; hp + 8 * nh; kl; kn]))) ss_gfL
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_free)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp SA hp nh n kl kn Hsp Hsplo Hsphi Hsp16 H21 H22 H20 H26 H19 HSAlo HSAhi
  Hhplo Hhp8 Hn0 Hnn Hnh Hhphi Hdisj Hkn Hkl V8 V72 V96 V128 V40 V48 VS VL HW1 HW2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (map (Z_to_bv 64) [hp; nh; hp + 8 * nh; kl; kn]))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 SA) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * n)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E26 : ew E 26 = Z_to_bv 64 (hp + 8 * n)) by (rewrite (EEo 26%nat 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 hp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nh)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hp + 8 * nh))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 kl)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 kn)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = SA) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = 8 * n) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = hp + 8 * n) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = hp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = nh) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = hp + 8 * nh) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = kl) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = kn) by (rewrite E36; apply unsigned_lit_small; lia).
assert (M1 : (hp + 8 * n) mod 8 = 0) by (rewrite Z.mul_comm, Z_mod_plus_full; exact Hhp8).
assert (M2 : (hp + 8 * nh) mod 8 = 0) by (rewrite Z.mul_comm, Z_mod_plus_full; exact Hhp8).
assert (M3 : (8 * n) mod 8 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
unfold ss_gfL. apply pa_entry_st_ok_full.
- unfold gf_regs. apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H19. symmetry. apply gfr_den. rewrite (gfr_U_sh E 26 (hp + 8 * n) 0 E26 E21) by lia.
  rewrite Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- unfold gf_regionsL, gf_frame, gf_sa, gf_slot, gf_last.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ sp 8 8 (gf_shE 22 40) ((SA + 40) / 8 + SHADOW_OFF));
        [apply gfr_den; apply (gfr_U_sh E 22 SA 40 E22 E21); lia
        | unfold SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]; lia|];
          assert ((SA + 40) / 8 <= SA + 40) by (apply Z.div_le_upper_bound; lia); zside
        | zside | exact V8].
    * apply (chunk_ok_val SEGS E _ sp 72 8 (gf_shE 22 48) ((SA + 48) / 8 + SHADOW_OFF));
        [apply gfr_den; apply (gfr_U_sh E 22 SA 48 E22 E21); lia
        | unfold SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]; lia|];
          assert ((SA + 48) / 8 <= SA + 48) by (apply Z.div_le_upper_bound; lia); zside
        | zside | exact V72].
    * apply (chunk_ok_val SEGS E _ sp 96 8 (SOff 22 48) (SA + 48));
        [apply gfr_den; exact (U_atom_off E 22 SA 48 E22 ltac:(lia) ltac:(lia)) | zside | zside | exact V96].
    * apply (chunk_ok_val SEGS E _ sp 128 8 (SOff 22 40) (SA + 40));
        [apply gfr_den; exact (U_atom_off E 22 SA 40 E22 ltac:(lia) ltac:(lia)) | zside | zside | exact V128].
  + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HW1 o Ho)|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ SA 40 8 (SOff 32 0) hp); [exact (gfr_den_atom E 32 hp E32) | zside | zside | exact V40].
    * apply (chunk_ok_val SEGS E _ SA 48 4 (SOff 33 0) nh); [exact (gfr_den_atom E 33 nh E33) | zside | zside | exact V48].
  + rewrite U26. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HW2 o Ho)|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (hp + 8 * n) 0 8 (SOff 36 0) kn); [exact (gfr_den_atom E 36 kn E36) | zside | zside |].
    rewrite Z.add_0_r. exact VS.
  + rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (hp + 8 * nh) (-8) 8 (SOff 35 0) kl); [exact (gfr_den_atom E 35 kl E35) | zside | zside |].
    replace (hp + 8 * nh + -8) with (hp + 8 * nh - 8) by lia. exact VL.
- apply pairwise_disjoint_of_extents.
  unfold gf_regionsL, gf_frame, gf_sa, gf_slot, gf_last, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, U22, U26, U34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hsplo Hsphi HSAlo HSAhi Hhplo Hn0 Hnn Hnh Hhphi Hdisj. clear. intros. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [gf_factsL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U21, U22, U26, U32, U34, U20, U33, U35, U36.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hsplo Hsphi Hsp16 HSAlo HSAhi Hhplo Hhp8 Hn0 Hnn Hnh Hhphi Hkn Hkl M1 M2 M3 C1. clear.
    unfold gf_ceil, SB, SHADOW_OFF. intros.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia).
  + cbn [gf_factsL f_alias alias_ok]. split; [|split; [|exact I]].
    * apply gfr_den_eq. rewrite gfr_U_add.
      -- rewrite (U_atom E 32 hp E32), (U_atom E 20 (8 * n) E20), (U_atom E 26 (hp + 8 * n) E26) by lia. reflexivity.
      -- rewrite (U_atom E 32 hp E32), (U_atom E 20 (8 * n) E20) by lia. lia.
    * apply gfr_den_eq.
      assert (USL : U E (SAlu ALU_SLL (SOff 33 0) (SLit 3)) = 8 * nh)
        by (rewrite gfr_U_sll3; rewrite (U_atom E 33 nh E33) by lia; lia).
      rewrite gfr_U_add; [|rewrite USL, (U_atom E 32 hp E32) by lia; lia].
      rewrite USL, (U_atom E 32 hp E32), (U_atom E 34 (hp + 8 * nh) E34) by lia. lia.
Qed.

(* ---- The entry state, variant E (the held key IS the last slot, nh = n + 1). ---- *)
Lemma gfr_entryE : forall (W : world SEGS) regs mem sp SA hp nh n kl kn,
spZ regs = sp -> alloc_ceiling + 16512 <= sp -> sp + 336 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 21 = w64 SHADOW_OFF -> getr regs 22 = w64 SA -> getr regs 20 = w64 (8 * n) ->
getr regs 26 = w64 (hp + 8 * n) -> getr regs 19 = w64 ((hp + 8 * n) / 8 + SHADOW_OFF) ->
4096 <= SA -> SA + 56 <= alloc_ceiling ->
4096 <= hp -> hp mod 8 = 0 -> 0 <= n -> nh = n + 1 -> nh < 2 ^ 26 -> hp + 8 * nh <= alloc_ceiling ->
(SA + 52 <= hp \/ hp + 8 * nh <= SA + 40) ->
4096 <= kn <= alloc_ceiling -> 0 <= kl < 2 ^ 64 ->
val_mem SEGS (arm W mem) (sp + 8) 8 ((SA + 40) / 8 + SHADOW_OFF) ->
val_mem SEGS (arm W mem) (sp + 72) 8 ((SA + 48) / 8 + SHADOW_OFF) ->
val_mem SEGS (arm W mem) (sp + 96) 8 (SA + 48) ->
val_mem SEGS (arm W mem) (sp + 128) 8 (SA + 40) ->
val_mem SEGS (arm W mem) (SA + 40) 8 hp ->
val_mem SEGS (arm W mem) (SA + 48) 4 nh ->
val_mem SEGS (arm W mem) (hp + 8 * n) 8 kn ->
(forall o, 48 <= o < 52 -> writable_at SEGS (arm W mem) (SA + o)) ->
(forall o, 0 <= o < 8 -> writable_at SEGS (arm W mem) (hp + 8 * n + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) [hp; nh; hp + 8 * nh; kl; kn]))) ss_gfE
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_free)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp SA hp nh n kl kn Hsp Hsplo Hsphi Hsp16 H21 H22 H20 H26 H19 HSAlo HSAhi
  Hhplo Hhp8 Hn0 Hnn Hnh Hhphi Hdisj Hkn Hkl V8 V72 V96 V128 V40 V48 VS HW1 HW2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (map (Z_to_bv 64) [hp; nh; hp + 8 * nh; kl; kn]))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 SA) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * n)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E26 : ew E 26 = Z_to_bv 64 (hp + 8 * n)) by (rewrite (EEo 26%nat 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 hp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nh)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E36 : ew E 36 = Z_to_bv 64 kn)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = SA) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = 8 * n) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = hp + 8 * n) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = hp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = nh) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = kn) by (rewrite E36; apply unsigned_lit_small; lia).
assert (M1 : (hp + 8 * n) mod 8 = 0) by (rewrite Z.mul_comm, Z_mod_plus_full; exact Hhp8).
assert (M3 : (8 * n) mod 8 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
unfold ss_gfE. apply pa_entry_st_ok_full.
- unfold gf_regs. apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H19. symmetry. apply gfr_den. rewrite (gfr_U_sh E 26 (hp + 8 * n) 0 E26 E21) by lia.
  rewrite Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- unfold gf_regionsE, gf_frame, gf_sa, gf_slot.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ sp 8 8 (gf_shE 22 40) ((SA + 40) / 8 + SHADOW_OFF));
        [apply gfr_den; apply (gfr_U_sh E 22 SA 40 E22 E21); lia
        | unfold SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]; lia|];
          assert ((SA + 40) / 8 <= SA + 40) by (apply Z.div_le_upper_bound; lia); zside
        | zside | exact V8].
    * apply (chunk_ok_val SEGS E _ sp 72 8 (gf_shE 22 48) ((SA + 48) / 8 + SHADOW_OFF));
        [apply gfr_den; apply (gfr_U_sh E 22 SA 48 E22 E21); lia
        | unfold SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]; lia|];
          assert ((SA + 48) / 8 <= SA + 48) by (apply Z.div_le_upper_bound; lia); zside
        | zside | exact V72].
    * apply (chunk_ok_val SEGS E _ sp 96 8 (SOff 22 48) (SA + 48));
        [apply gfr_den; exact (U_atom_off E 22 SA 48 E22 ltac:(lia) ltac:(lia)) | zside | zside | exact V96].
    * apply (chunk_ok_val SEGS E _ sp 128 8 (SOff 22 40) (SA + 40));
        [apply gfr_den; exact (U_atom_off E 22 SA 40 E22 ltac:(lia) ltac:(lia)) | zside | zside | exact V128].
  + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HW1 o Ho)|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ SA 40 8 (SOff 32 0) hp); [exact (gfr_den_atom E 32 hp E32) | zside | zside | exact V40].
    * apply (chunk_ok_val SEGS E _ SA 48 4 (SOff 33 0) nh); [exact (gfr_den_atom E 33 nh E33) | zside | zside | exact V48].
  + rewrite U26. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HW2 o Ho)|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (hp + 8 * n) 0 8 (SOff 36 0) kn); [exact (gfr_den_atom E 36 kn E36) | zside | zside |].
    rewrite Z.add_0_r. exact VS.
- apply pairwise_disjoint_of_extents.
  unfold gf_regionsE, gf_frame, gf_sa, gf_slot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, U22, U26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hsplo Hsphi HSAlo HSAhi Hhplo Hn0 Hnn Hnh Hhphi Hdisj. clear. intros. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [gf_factsE f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U21, U22, U26, U32, U20, U33, U36.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hsplo Hsphi Hsp16 HSAlo HSAhi Hhplo Hhp8 Hn0 Hnn Hnh Hhphi Hkn M1 M3 C1. clear.
    unfold gf_ceil, SB, SHADOW_OFF. intros.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia).
  + cbn [gf_factsE f_alias alias_ok]. split; [|split; [|exact I]].
    * apply gfr_den_eq. rewrite gfr_U_add.
      -- rewrite (U_atom E 32 hp E32), (U_atom E 20 (8 * n) E20), (U_atom E 26 (hp + 8 * n) E26) by lia. reflexivity.
      -- rewrite (U_atom E 32 hp E32), (U_atom E 20 (8 * n) E20) by lia. lia.
    * apply gfr_den_eq.
      assert (USL : U E (SAlu ALU_SLL (SOff 33 0) (SLit 3)) = 8 * nh)
        by (rewrite gfr_U_sll3; rewrite (U_atom E 33 nh E33) by lia; lia).
      rewrite gfr_U_add; [|rewrite USL, (U_atom E 32 hp E32) by lia; lia].
      rewrite USL, (U_atom E 32 hp E32), (U_atom_off E 26 (hp + 8 * n) 8 E26) by lia. lia.
Qed.

Lemma gfr_mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd. rewrite Hd.
replace (16 * (x / 16)) with ((x / 16 * 2) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma gfr_not_wrange : forall E rs a,
Forall (fun r => ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)) rs ->
~ in_wrange E rs a.
Proof. intros E rs a HF (r & Hin & Hr). rewrite Forall_forall in HF. exact (HF r Hin Hr). Qed.

Lemma gfr_in_rm : forall (x y : Z * Z) l1 l2, In x (l1 ++ y :: l2) -> x <> y -> In x (l1 ++ l2).
Proof.
intros x y l1 l2 H Hne. apply in_app_or in H as [H | [H | H]].
- apply in_or_app. left. exact H.
- exfalso. apply Hne. symmetry. exact H.
- apply in_or_app. right. exact H.
Qed.

(* A block of the relay entry that was live at drain's entry is in drain's footprint dFP: the entry's
   Permutation puts it in one of the footprint's three lists, or it is the table block or one of dxrest,
   and then it occurs twice in the state's list of blocks. *)
Lemma gfr_fp : forall cx ly S (W : world SEGS) mem md e h OC out b m,
AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) (ablocks B (dxly cx) (dxS cx)) ->
forall i, 0 <= i < req_size m -> inFP (dFP cx) (b + i).
Proof.
intros cx ly S W mem md e h OC out b m HAR HP1 HP0 Hae Hm Hin0 i Hi.
apply (Permutation_in _ HP0) in Hin0.
assert (HFP : In (b, m) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx)) ->
  inFP (dFP cx) (b + i)).
{ intros Hx. unfold dFP, dr_fp. exists (b, b + req_size m).
  split; [right; exact (in_map (fun b0 => (fst b0, fst b0 + req_size (snd b0))) _ (b, m) Hx)|].
  cbn [fst snd]. lia. }
destruct Hin0 as [Hg | Hin0].
- exfalso. rewrite Hg in HP1.
  exact (gfr_dup_in ly S W mem md [] _ (b, m) HAR HP1 (in_or_app _ _ _ (or_introl Hae)) Hm).
- apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; right; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hx]; [apply HFP; apply in_or_app; right; apply in_or_app; right; exact Hx|].
  exfalso. apply in_split in Hae as (a1 & a2 & Ea). rewrite Ea, <- app_assoc in HP1.
  apply (gfr_dup_in ly S W mem md ((dxG cx, ATABLE) :: a1) (a2 ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx)
    (b, m) HAR HP1); [|exact Hm].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hx.
Qed.

(* A byte of a block of the relay entry is one drain may write: in its footprint and a live block, or a block
   drain itself allocated. *)
Lemma gfr_awr_blk : forall cx ly S (W : world SEGS) mem md e h OC out b m blc lyq a,
AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) blc -> b <= a < b + req_size m ->
awr_byte DRAIN_STK (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq [] a.
Proof.
intros cx ly S W mem md e h OC out b m blc lyq a HAR HP1 HP0 Hae Hm Hinc Ha.
assert (DZ : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec DZ (b, m) (ablocks B (dxly cx) (dxS cx))) as [Hin0 | Hnin0].
- right; left. split.
  + replace a with (b + (a - b)) by lia.
    apply (gfr_fp cx ly S W mem md e h OC out b m HAR HP1 HP0 Hae Hm Hin0). lia.
  + exists b, m. split; [exact Hinc | exact Ha].
- right; right; left. exists b, m. split; [exact Hinc|]. split; [exact Hnin0 | exact Ha].
Qed.

(* A region inside a block that survives a call keeps its bytes (the call's acall_kept) and the presence of
   its window (the block is still live after the call). *)
Lemma gfr_kept_blk : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
  ly2 S2 md2 n lo hi wlo whi cs b m base,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
AR SEGS B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = base -> In (b, m) (ablocks B lyc Sc) ->
b <= base + lo -> base + hi <= b + req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b <= a < b + req_size m -> ~ Er a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er ly2 S2 md2 n lo hi wlo whi cs b m base (_ & K2 & _) HAR2 Hin2 Hn Hin
  H1 H2 H3 H4 HnE.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. apply HnE. lia.
- intros _. apply (apresent_writable SEGS). exact (proj1 (Hpres a ltac:(lia))).
Qed.

Lemma gfr_apresent_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
assert (Hx : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
specialize (Hg _ Hx). unfold mrestrict in Hg. rewrite Hh in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; reflexivity].
Qed.

(* The arm's post from its three steps: run 1 (W1, m1 -> mR1), the free (-> W2, mem2), run 2 (mem2 -> m2).
   Both runs write only s->nheld [SA + 48, SA + 52) and s->held[n] [hp + 8 n, + 8); the free changes the freed
   key's block and the stack below the frame. *)
Lemma gfr_post : forall cx e1 n ly1 S1 (W1 : world SEGS) m1 md1 mR1 k1 ly2 S2 (W2 : world SEGS) mem2 md2' m2 md2
  regs1 regs2 l1 l2,
AR SEGS B ly1 S1 W1 m1 md1 -> AR SEGS B ly2 S2 W2 mem2 md2' ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) -> dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE ->
In (re_hp e1, re_kh e1) (ablocks B ly1 S1) -> re_hp e1 + 8 * Z.of_nat n + 8 <= re_hp e1 + req_size (re_kh e1) ->
In (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) (ablocks B ly1 S1) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W1) mR1 aa = aview SEGS (w_H W1) m1 aa) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W2) m2 aa = aview SEGS (w_H W2) mem2 aa) ->
acall_kept SEGS B ly1 S1 W1 mR1 W2 mem2 (dsp0 cx + - DRAIN_FRAME - ASTACK) (dsp0 cx + - DRAIN_FRAME)
  (fun a => key_addr (gf_key e1 n) <= a <
     key_addr (gf_key e1 n) + req_size (Z.of_nat (length (key_text (gf_key e1 n))) + 1)) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) mR1) ->
mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) m2) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (key_addr (gf_key e1 n) <= a <
     key_addr (gf_key e1 n) + req_size (Z.of_nat (length (key_text (gf_key e1 n))) + 1)) ->
  apresent (w_H W1) mR1 a -> apresent (w_H W2) mem2 a) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) mR1 (as_errno B + i)) ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 m2 md2 (k1 + 1) ->
frames S2 = frames S1 ->
ablocks B ly1 S1 = l1 ++ (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: l2 ->
ablocks B ly2 S2 = l1 ++ l2 ->
mo_le MT S1 S2 (mo_free MT) ->
aregs_preserved regs1 regs2 ->
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1 - 1) ->
val_mem SEGS (arm W2 m2) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1)) ->
GFPOST cx e1 n ly1 S1 W1 m1 k1 ly2 S2 W2 m2 md2 regs1 regs2.
Proof.
intros cx e1 n ly1 S1 W1 m1 md1 mR1 k1 ly2 S2 W2 mem2 md2' m2 md2 regs1 regs2 l1 l2 HAR1 HAR2 HGin1 HGle HSAle
  HHin Hslot Kkb KR1 KR2 (K1 & K2 & K3 & K4 & K5 & K6) HGr1 HGr2 Hpres2 Herr2 HJf Hfr2 Ebl1 Ebl2 Hmle2 HPR V1 V2.
pose proof asan_consts as (C1 & _).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 HGin1) as (_ & HG4096 & HGceil & _).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 HHin) as (_ & Hh4096 & Hhceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
assert (WSA : forall x, dxSA cx + 48 <= x < dxSA cx + 52 -> dxG cx <= x < dxG cx + req_size ATABLE)
  by (intros x Hx; rewrite RQT; clear - Hx HGle HSAle; unfold AENT, ATABLE in *; lia).
assert (WSL : forall x, re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8 ->
  re_hp e1 <= x < re_hp e1 + req_size (re_kh e1)) by (intros x Hx; clear - Hx Hslot; lia).
assert (NIMG : forall x, in_img SEGS x ->
  ~ (dxSA cx + 48 <= x < dxSA cx + 52) /\ ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8)).
{ intros x Hx. split; intros Hw.
  - exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR1 HGin1 (WSA x Hw) Hx).
  - exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR1 HHin (WSL x Hw) Hx). }
unfold GFPOST.
split; [exact HPR|]. split; [exact HJf|]. split; [exact Hfr2|].
split; [exists l1, l2; split; [exact Ebl1 | exact Ebl2]|]. split; [exact Hmle2|].
split.
{ intros b m i Hbm Hi Hex. unfold GFEXC in Hex.
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hbm) as (_ & Hb4096 & Hbceil & _).
  assert (Hr : 0 <= b + i < 2 ^ 64) by (clear - Hb4096 Hbceil Hi C1; lia).
  rewrite (KR2 _ Hr (fun H => Hex (or_intror (or_introl H))) (fun H => Hex (or_intror (or_intror H)))).
  rewrite (K2 b m i Hbm Hi (fun H => Hex (or_introl H))).
  exact (KR1 _ Hr (fun H => Hex (or_intror (or_introl H))) (fun H => Hex (or_intror (or_intror H)))). }
split.
{ intros x Hi Hno Herr. destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64) by (pose proof (pa_segs_low x Hi); unfold kLowMemEnd in *; lia).
  rewrite (KR2 x Hr N1 N2), (K3 x Hi Hno Herr). exact (KR1 x Hr N1 N2). }
split.
{ intros x Hx Hns.
  assert (N1 : ~ (dxSA cx + 48 <= x < dxSA cx + 52)) by (clear - Hx HSAle HGceil; unfold AENT, ATABLE in *; lia).
  assert (N2 : ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8))
    by (clear - Hx Hslot Hhceil; lia).
  assert (Hr : 0 <= x < 2 ^ 64) by (clear - Hx C1; lia).
  rewrite (KR2 x Hr N1 N2), (K1 x Hx ltac:(clear - Hns; lia)). exact (KR1 x Hr N1 N2). }
split.
{ intros x Hx Hns Hp.
  apply (gfr_apresent_grows _ _ _ _ HGr2). apply K5; [exact Hx | clear - Hns; lia |].
  exact (gfr_apresent_grows _ _ _ _ HGr1 Hp). }
split.
{ intros x Hi Hno Herr Hp.
  assert (Hnot : forall ly0 S0 (W0 : world SEGS) m0 md0, AR SEGS B ly0 S0 W0 m0 md0 -> ~ aowned B ly0 S0 x)
    by (intros ly0 S0 W0 m0 md0 HA Ho; apply Hno; exact (proj1 (al_owned_image SEGS B LAWS ly0 S0 W0 m0 md0 x HA Hi) Ho)).
  apply (gfr_apresent_grows _ _ _ _ HGr2).
  apply (Hpres2 x Hi (Hnot _ _ _ _ _ HAR1) (Hnot _ _ _ _ _ HAR2) Herr).
  - intros Hk. exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR1 Kkb Hk Hi).
  - exact (gfr_apresent_grows _ _ _ _ HGr1 Hp). }
split.
{ intros i Hi.
  assert (Hin : inG (G_DR B RG) (as_errno B + i)).
  { unfold inG. apply Exists_exists. exists (as_errno B, 4). split.
    - unfold G_DR, G_SL. cbn [In]. repeat first [left; reflexivity | right].
    - unfold in_zr. cbn [fst snd]. lia. }
  destruct (HG _ Hin) as (Hi2 & _). destruct (NIMG _ Hi2) as (N1 & N2).
  assert (Hr : 0 <= as_errno B + i < 2 ^ 64) by (pose proof (pa_segs_low _ Hi2); unfold kLowMemEnd in *; lia).
  rewrite (KR2 _ Hr N1 N2), (Herr2 i Hi). exact (KR1 _ Hr N1 N2). }
split; [exact V1 | exact V2].
Qed.

(* =========================================================================================================
   THE ARM.
   ========================================================================================================= *)
Theorem gs_free : gs_free_stmt B MT MMAX RG.
Proof.
intros cx s1 D p q W1 c1 HB HGF HN.
destruct HGF as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  jj & n & Hcfg & HRL & R23 & R24 & R19 & R26 & R20 & V8 & V72 & Hnlt & Hges & Hjj & Hidx & HGSF & HCORE & HFUT).
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRST & HBUD).
pose proof HDMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT & HLIVE & HPERM).
pose proof HRL as (Usp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR2 & V192 & V200 & V56 & V48 & V64).
pose proof HFR2 as (F208 & F96 & F128 & _).
pose proof HB as (HPRE & HSA10 & HGin0 & HGle & HSAle & HGARR0 & HAWR0 & HENT0 & HB9 & HB10 & HB11 & HB12 & HB13 &
  HB14 & HB15 & HB16 & HPERM0 & HB18 & HB19 & HB20 & HB21 & HB22 & HMOK).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp & Htp & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (ajournal_gx_AR SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK = 16848) by reflexivity.
assert (WF : DRAIN_FRAME = 336) by reflexivity.
assert (Hsp0 : alloc_ceiling + 16848 <= dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - WS Hceil Hslo Hshi H47; lia).
assert (Hsp16 : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
  by (unfold dsp0; rewrite WF, Zminus_mod, Hal16; reflexivity).
(* the relay's table block *)
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGapp, HGpres.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in HGle; clear - HGle HG4096; lia).
assert (HSAhi : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; clear - HSAle HGceil; lia).
(* the relay entry and its held array *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KF).
assert (HNH : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
destruct KHP as [(_ & Hk0) | (Hhp0 & HHin & Hkh & Hkh8 & HGA)].
{ exfalso. rewrite Hk0 in Hnlt. cbn [length] in Hnlt. clear - Hnlt. lia. }
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 HHin) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _).
assert (RQH : req_size (re_kh e1) = re_kh e1) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
rewrite RQH in Hhceil, Hhapp, Hhpres.
assert (Hkin : In (gf_key e1 n) (re_keys e1)) by (unfold gf_key; apply nth_In; exact Hnlt).
assert (Hlin : In (gf_lastkey e1) (re_keys e1)) by (unfold gf_lastkey; apply nth_In; lia).
destruct (proj1 (Forall_forall _ _) KF _ Hkin) as (Kkb & Kkg & Kknz & Kklen).
destruct (proj1 (Forall_forall _ _) KF _ Hlin) as (Klb & Klg & Klnz & Kllen).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Kkb) as (Hk16 & Hk4096 & Hkceil & Hkapp & Hkpres & _).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Klb) as (_ & Hl4096 & Hlceil & _).
pose proof (req_size_pos (Z.of_nat (length (key_text (gf_key e1 n))) + 1) ltac:(lia)) as (RQK1 & RQK2).
pose proof (req_size_pos (Z.of_nat (length (key_text (gf_lastkey e1))) + 1) ltac:(lia)) as (RQL1 & RQL2).
(* the cells the state reads *)
assert (VH40 : val_mem SEGS (arm W1 m1) (dxSA cx + 40) 8 (re_hp e1))
  by (apply (gf_entry_hp W1 m1 _ e1 Kp1); [clear - Hh4096 Hhceil Hkh8 C1; lia | exact HENTB]).
assert (VH48 : val_mem SEGS (arm W1 m1) (dxSA cx + 48) 4 (re_nheld e1))
  by (apply (gf_entry_nheld W1 m1 _ e1 Kp1); [clear - KNH HNH; lia | exact HENTB]).
assert (VS : val_mem SEGS (arm W1 m1) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_key e1 n)))
  by (apply (gf_ptrs_slot W1 m1 (re_hp e1) (re_keys e1) n Hnlt); [change (nth n (re_keys e1) gf_k0) with (gf_key e1 n);
      clear - Hk4096 Hkceil RQK1 C1; lia | exact HGA]).
assert (VL : val_mem SEGS (arm W1 m1) (re_hp e1 + 8 * re_nheld e1 - 8) 8 (key_addr (gf_lastkey e1))).
{ replace (re_hp e1 + 8 * re_nheld e1 - 8) with (re_hp e1 + 8 * Z.of_nat (length (re_keys e1) - 1))
    by (rewrite HNH; clear - Hnlt; lia).
  apply (gf_ptrs_slot W1 m1 (re_hp e1) (re_keys e1) (length (re_keys e1) - 1) ltac:(clear - Hnlt; lia));
    [change (nth (length (re_keys e1) - 1) (re_keys e1) gf_k0) with (gf_lastkey e1); clear - Hl4096 Hlceil RQL1 C1; lia
    | exact HGA]. }
(* the table block and the held array are two different blocks *)
assert (HNEGH : (dxG cx, ATABLE) <> (re_hp e1, re_kh e1)).
{ intros Heq. apply (gfr_dup_in ly1 S1 W1 m1 md1 [] _ (dxG cx, ATABLE) HAR1 HPERM); [|cbn [snd]; unfold ATABLE; lia].
  apply in_or_app. left. rewrite Heq. unfold aentry_blks. rewrite (proj2 (Z.eqb_neq _ _) Hhp0).
  apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR1 HGin1 HHin HNEGH) as DGH.
rewrite RQT, RQH in DGH. unfold zdisjoint in DGH. cbn [fst snd] in DGH.
assert (HDSH : dxSA cx + 52 <= re_hp e1 \/ re_hp e1 + 8 * re_nheld e1 <= dxSA cx + 40)
  by (unfold ATABLE, AENT in *; clear - DGH HGle HSAle Hkh; lia).
assert (HW1 : forall o, 48 <= o < 52 -> writable_at SEGS (arm W1 m1) (dxSA cx + o))
  by (intros oo Hoo; apply HAWR; unfold AENT; lia).
assert (HW2 : forall o, 0 <= o < 8 -> writable_at SEGS (arm W1 m1) (re_hp e1 + 8 * Z.of_nat n + o))
  by (intros oo Hoo; apply (apresent_writable SEGS);
      exact (proj1 (Hhpres (re_hp e1 + 8 * Z.of_nat n + oo) ltac:(rewrite HNH in Hkh; clear - Hkh Hnlt Hoo; lia)))).
(* the three blocks the arm touches: the table block, the held array and the freed key's text *)
assert (HHae : In (re_hp e1, re_kh e1) (aentry_blks e1)).
{ unfold aentry_blks. rewrite (proj2 (Z.eqb_neq _ _) Hhp0). apply in_or_app. right. apply in_or_app. left. left.
  reflexivity. }
assert (HKae : In (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) (aentry_blks e1)).
{ unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
  exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hkin). }
assert (HAEG : forall x, In x (aentry_blks e1) -> x <> (dxG cx, ATABLE)).
{ intros x Hx Heq. subst x. apply (gfr_dup_in ly1 S1 W1 m1 md1 [] _ (dxG cx, ATABLE) HAR1 HPERM);
    [apply in_or_app; left; exact Hx | cbn [snd]; unfold ATABLE; lia]. }
assert (HKH : (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) <> (re_hp e1, re_kh e1)).
{ intros Heq. pose proof HPERM as HP'. unfold aentry_blks in HP'.
  rewrite (proj2 (Z.eqb_neq _ _) Hhp0), <- !app_assoc in HP'. cbn [app] in HP'.
  eapply (gfr_dup_in ly1 S1 W1 m1 md1 ((dxG cx, ATABLE) :: (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]))
    _ (re_hp e1, re_kh e1) HAR1 HP').
  - apply in_or_app. left. rewrite <- Heq.
    exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hkin).
  - cbn [snd]. lia. }
pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR1 HGin1 Kkb (fun Heq => HAEG _ HKae (eq_sym Heq)))
  as DGK.
pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR1 HHin Kkb (fun Heq => HKH (eq_sym Heq))) as DHK.
rewrite RQT in DGK. rewrite RQH in DHK. unfold zdisjoint in DGK, DHK. cbn [fst snd] in DGK, DHK.
(* the free's budget: the trace still owed starts with this free *)
destruct (gsf_fut cx s1 p q jj n a jb o ha ks tl HGSF Hges Hidx HFUT) as (tl2 & jb2 & Etl & Hfut2).
assert (HMOKF : mo_ok MT S1 (mo_free MT)).
{ destruct HBUD as (Hmle & Hsp00 & Hcost & Hbb & Hmax).
  assert (HTC2 : 0 <= tr_cost MT tl2).
  { (* every request still owed asks a nonnegative size (W_drain_tr.v): the six signs of the next round state
       dnext s1, four of them through the line loop at S q, the expected list's two from the cut's DLINK *)
    pose proof HRST as (_ & HJ1 & HCU & _). destruct HJ1 as (_ & _ & _ & HNZ).
    pose proof HLINK as (_ & _ & _ & _ & L5 & _ & _ & _ & _ & L10 & L11 & _).
    pose proof HHIST as (_ & _ & _ & _ & _ & D6 & _).
    cbn [dvirt drain_b_c.ds_ka drain_b_c.ds_en drain_b_c.ds_ecap drain_b_c.ds_no] in L5, L10, L11, D6.
    pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & HOC).
    cbn [dvirt drain_b_c.ds_ocap] in HOC.
    pose proof HB15 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hmx & HnoO & _).
    pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEXP & _).
    pose proof HEXP as (_ & _ & _ & _ & (HEn & _) & _).
    destruct (gsf_line cx s1 p q jj n HGSF Hges Hidx) as (_ & _ & _ & HdbS & _ & G1 & G2 & _ & G4).
    assert (Hka : 0 <= dlka cx s1 p)
      by (rewrite <- L5; unfold drain_b_c.ent_ka; destruct (re_hp e1 =? 0); clear - Hkh8; lia).
    assert (Hoc : 0 <= GSoc cx s1 p q) by (clear - HOC; destruct HOC as [(Hc0 & _) | (Hc0 & _)]; lia).
    assert (Hno : 0 <= GSno cx s1 p q) by (rewrite D6; clear - HnoO; lia).
    destruct (gs_dnext_signs_at cx s1 (S q) HNZ HdbS ltac:(clear - HCU; unfold ulen in HCU; lia)
      ltac:(rewrite G1; exact Hno) ltac:(rewrite G2; exact Hoc) ltac:(rewrite G4; exact Hka))
      as (S1c & S1o & S1n & S1k).
    assert (He : 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1)) by (rewrite <- L10; unfold hl_n; lia).
    assert (Hec : 0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1))
      by (rewrite <- L11; unfold hl_n in HEn; lia).
    pose proof (gs_dsfut_sizes cx _ a _ _ _ _ _ _ jb o ha ks tl ltac:(clear - Hmx; lia) Hoc S1c S1o S1n He Hec S1k
      HFUT) as Hsz.
    rewrite Etl in Hsz. apply Forall_inv_tail in Hsz. exact (gs_tr_cost_nonneg MT MTL tl2 Hsz). }
  apply (mok_station MT (dxS cx) S1 _ spent (mo_free MT) MTL HMOK Hmle (mo_free_nonneg MT MTL)).
  assert (TC : tr_cost MT tl = mo_free MT + tr_cost MT tl2) by (rewrite Etl; reflexivity).
  rewrite TC in Hcost. lia. }
subst c1. unfold cfg_at.
remember (Eimg (Ereg regs1 (map (Z_to_bv 64) [re_hp e1; re_nheld e1; re_hp e1 + 8 * re_nheld e1;
  key_addr (gf_lastkey e1); key_addr (gf_key e1 n)]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs1 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E2 : ew E 2 = getr regs1 2) by exact (EA 2%nat ltac:(lia)).
assert (E3 : ew E 3 = getr regs1 3) by exact (EA 3%nat ltac:(lia)).
assert (E4 : ew E 4 = getr regs1 4) by exact (EA 4%nat ltac:(lia)).
assert (E8 : ew E 8 = w64 ((rg_s RG + 4) / 8)) by exact (eq_trans (EA 8%nat ltac:(lia)) R8).
assert (E22 : ew E 22 = w64 (dxSA cx)) by exact (eq_trans (EA 22%nat ltac:(lia)) R22).
assert (E21 : ew E 21 = w64 SHADOW_OFF) by exact (eq_trans (EA 21%nat ltac:(lia)) R21).
assert (E26 : ew E 26 = w64 (re_hp e1 + 8 * Z.of_nat n)) by exact (eq_trans (EA 26%nat ltac:(lia)) R26).
assert (E34 : ew E 34 = Z_to_bv 64 (re_hp e1 + 8 * re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E36 : ew E 36 = Z_to_bv 64 (key_addr (gf_key e1 n)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 (key_addr (gf_lastkey e1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Hr26 : 0 <= re_hp e1 + 8 * Z.of_nat n < 2 ^ 64)
  by (rewrite HNH in Hkh; clear - Hh4096 Hhceil Hkh Hnlt C1; lia).
assert (Bsp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Usp).
assert (B22 : bv_unsigned (ew E 22) = dxSA cx)
  by (rewrite E22; apply unsigned_lit_small; clear - HSAlo HSAhi C1; lia).
assert (B26 : bv_unsigned (ew E 26) = re_hp e1 + 8 * Z.of_nat n)
  by (rewrite E26; apply unsigned_lit_small; rewrite HNH in Hkh; clear - Hh4096 Hhceil Hkh Hnlt C1; lia).
assert (B34 : bv_unsigned (ew E 34) = re_hp e1 + 8 * re_nheld e1)
  by (rewrite E34; apply unsigned_lit_small; rewrite HNH in Hkh |- *; clear - Hh4096 Hhceil Hkh C1; lia).
assert (UBx : U E gf_Bx = SHADOW_OFF) by (unfold gf_Bx; apply (U_atom E 21 SHADOW_OFF E21); unfold SHADOW_OFF; lia).
assert (U22 : U E (SOff 22 0) = dxSA cx) by (rewrite U_SOff, B22, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (U26 : U E (SOff 26 0) = re_hp e1 + 8 * Z.of_nat n)
  by (rewrite U_SOff, B26, Z.add_0_r; apply zcanon_id; unfold M64; rewrite HNH in Hkh;
      clear - Hh4096 Hhceil Hkh Hnlt C1; lia).
assert (U34 : U E (SOff 34 0) = re_hp e1 + 8 * re_nheld e1)
  by (rewrite U_SOff, B34, Z.add_0_r; apply zcanon_id; unfold M64; rewrite HNH in Hkh |- *;
      clear - Hh4096 Hhceil Hkh C1; lia).
destruct (Nat.eq_dec n (length (re_keys e1) - 1)) as [HnE | HnL].
- (* ===== variant E: the held key IS the last slot (n = nheld - 1); three regions ===== *)
  assert (KL : gf_lastkey e1 = gf_key e1 n) by (unfold gf_lastkey, gf_key; rewrite <- HnE; reflexivity).
  pose proof (gfr_entryE W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1) (Z.of_nat n)
    (key_addr (gf_lastkey e1)) (key_addr (gf_key e1 n)) Usp ltac:(rewrite WF; clear - Hsp0; lia)
    ltac:(rewrite WF; clear - Hsp0; lia) Hsp16 R21 R22 R20 R26 R19 HSAlo HSAhi Hh4096
    (gfr_mod16_8 _ Hh16)
    (Nat2Z.is_nonneg n) ltac:(rewrite HNH; clear - Hnlt HnE; lia) ltac:(clear - KNH; lia)
    ltac:(rewrite HNH in Hkh |- *; clear - Hkh Hhceil; lia) HDSH
    ltac:(clear - Hk4096 Hkceil RQK1; lia) ltac:(clear - Hl4096 Hlceil RQL1 C1; lia)
    V8 V72 F96 F128 VH40 VH48 VS HW1 HW2) as HS.
  rewrite <- HE in HS. clear HE.
  assert (SHOK : sh_ok SEGS gf_Bx gf_SHE E (mrestrict (w_H W1) m1)).
  { unfold sh_ok, gf_SHE. constructor; [|constructor; [|constructor]].
    - apply (gfr_shent E ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR1 HHin UBx U26);
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent E ly1 S1 W1 m1 md1 (dxG cx) ATABLE 22 _ 40 52 HAR1 HGin1 UBx U22);
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  paj_run_tok RUN HS HJ SHOK gf_Bspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26 in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk cx ly1 S1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HGr1. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  assert (KR1 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W1) (ms_mem ms1) aa = aview SEGS (w_H W1) m1 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22, ?B26; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Bsp).
  destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
  assert (Has : ASTACK = 16384) by reflexivity.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  eapply SRr_bind.
  { rewrite (pal_free B TL).
    eapply (AFREE W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS
      (dxmd cx) [] ly1 S1 _ k1 (key_addr (gf_key e1 n)) (Z.of_nat (length (key_text (gf_key e1 n))) + 1)
      (- DRAIN_FRAME) _ [] HJi Kkb).
    - rewrite Q10, E36. reflexivity.
    - rewrite Usp1. lia.
    - rewrite WF. reflexivity.
    - rewrite WF. lia.
    - rewrite Has, WS, WF. lia.
    - rewrite Q3, E3, R3. exact Hgp.
    - rewrite Q4, E4, R4. exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HGSB as (HG1 & HG2 & _).
      assert (HD8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] (ms_regs ms1)).
      + apply achain_low. clear - HD8 HG2 C1. unfold ASRC in *. lia.
      + rewrite Usp1, WF. clear - Hsp0. lia.
      + unfold s0Z. rewrite Q8, E8. unfold w64. apply unsigned_lit_small. clear - HD8 HG2. unfold ASRC in *. lia.
      + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
    - intros Hin0 i Hi.
      exact (gfr_fp cx ly1 S1 W1 m1 md1 e1 h1 _ out1 _ _ HAR1 HPERM HPERM0 HKae ltac:(lia) Hin0 i Hi).
    - exact HMOKF. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (l1 & l2 & Ebl1 & Ebl2) & Hfr2 &
    Hkept2 & Hmle2 & Herr2 & Hpres2).
  pose proof (proj1 HJ2i) as HAR2.
  assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)).
  { pose proof HGin1 as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HAEG _ HKae (eq_sym Heq))). }
  assert (HHin2 : In (re_hp e1, re_kh e1) (ablocks B ly2 S2)).
  { pose proof HHin as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HKH (eq_sym Heq))). }
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_stack_aj; [exact Hkept2 | exact HJ2i | exact Bsp | ..]; rewrite ?WS, ?WF; lia.
    - apply (gfr_kept_blk E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 md2 22 40 52 48 52 _ (dxG cx) ATABLE (dxSA cx)
        Hkept2 HAR2 HGin2 B22 HGin1); rewrite ?RQT;
        [clear - HGle HSAle; unfold AENT, ATABLE in *; lia | clear - HGle HSAle; unfold AENT, ATABLE in *; lia
        | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DGK; lia].
    - apply (gfr_kept_blk E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 md2 26 0 8 0 8 _ (re_hp e1) (re_kh e1)
        (re_hp e1 + 8 * Z.of_nat n) Hkept2 HAR2 HHin2 B26 HHin); rewrite ?RQH;
        [lia | rewrite HNH in Hkh; clear - Hkh Hnlt; lia | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DHK; lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall mm, (mm < 48)%nat -> ew Ea mm = ew E mm)
    by (intros mm Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  clear HEa.
  assert (UEa : forall k, (k < 48)%nat -> U Ea (SOff k 0) = U E (SOff k 0))
    by (intros k Hk; rewrite !U_SOff, (OLDa k Hk); reflexivity).
  assert (B22a : bv_unsigned (ew Ea 22) = dxSA cx) by (rewrite OLDa by lia; exact B22).
  assert (B26a : bv_unsigned (ew Ea 26) = re_hp e1 + 8 * Z.of_nat n) by (rewrite OLDa by lia; exact B26).
  assert (HJ2 : @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1)).
  { apply (ajournal_gx_pack SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
      (dxmem cx) (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1) memS);
      [exact HSTK1 | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | intros aa Haa; lia]. }
  assert (UBxa : U Ea gf_Bx = SHADOW_OFF) by (unfold gf_Bx in *; rewrite UEa by lia; exact UBx).
  assert (SHOK2 : sh_ok SEGS gf_Bx gf_SHE Ea (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, gf_SHE. constructor; [|constructor; [|constructor]].
    - apply (gfr_shent Ea ly2 S2 W2 mem2 md2 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR2 HHin2 UBxa
        ltac:(rewrite UEa by lia; exact U26));
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent Ea ly2 S2 W2 mem2 md2 (dxG cx) ATABLE 22 _ 40 52 HAR2 HGin2 UBxa
        ltac:(rewrite UEa by lia; exact U22));
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  paj_run_to_tok RUNTO HS HJ2 SHOK2 gf_Bspan A_dr_next.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22a in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26a in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk cx ly1 S1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin2).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_nil. }
  rename HFr into HFr2, HG0 into HGr2. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  assert (KR2 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W2) (ms_mem msf) aa = aview SEGS (w_H W2) mem2 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msf) HFr2 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22a, ?B26a; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (20%bv : bv 5) F20.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26.
  prreg HS (27%bv : bv 5) F27.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ev ss ms 19%bv HS) as F19;
    let e := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in change (sr_get (ss_regs ss) 19%bv) with e in F19;
    set (Ef := Ev) in HS, F19 end.
  cbn [ms_regs restrict mkst] in F19.
  assert (UF : forall mm, (mm < 512)%nat -> ew Ef mm = ew Ea mm)
    by (intros mm Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (HPR : aregs_preserved regs1 (ms_regs msf)).
  { apply aregs_preserved_eqs.
    - rewrite F2, OLDa by lia. exact (EA 2%nat ltac:(lia)).
    - rewrite F3, OLDa by lia. exact (EA 3%nat ltac:(lia)).
    - rewrite F4, OLDa by lia. exact (EA 4%nat ltac:(lia)).
    - rewrite F8, OLDa by lia. exact (EA 8%nat ltac:(lia)).
    - rewrite F9, OLDa by lia. exact (EA 9%nat ltac:(lia)).
    - rewrite F18, OLDa by lia. exact (EA 18%nat ltac:(lia)).
    - rewrite F19, R19. apply gfr_den.
      assert (Ef26 : ew Ef 26 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite UF, OLDa by lia; exact E26).
      assert (Ef21 : ew Ef 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite UF, OLDa by lia; exact E21).
      pose proof (gfr_U_sh Ef 26 (re_hp e1 + 8 * Z.of_nat n) 0 Ef26 Ef21 Hr26 ltac:(rewrite Z.add_0_r; exact Hr26))
        as X.
      rewrite Z.add_0_r in X. exact X.
    - rewrite F20, OLDa by lia. exact (EA 20%nat ltac:(lia)).
    - rewrite F21, OLDa by lia. exact (EA 21%nat ltac:(lia)).
    - rewrite F22, OLDa by lia. exact (EA 22%nat ltac:(lia)).
    - rewrite F23, OLDa by lia. exact (EA 23%nat ltac:(lia)).
    - rewrite F24, OLDa by lia. exact (EA 24%nat ltac:(lia)).
    - rewrite F25, OLDa by lia. exact (EA 25%nat ltac:(lia)).
    - rewrite F26, OLDa by lia. exact (EA 26%nat ltac:(lia)).
    - rewrite F27, OLDa by lia. exact (EA 27%nat ltac:(lia)). }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSA.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RSL.
  cbn [ms_mem restrict] in RSA, RSL.
  assert (VF1 : val_mem SEGS (arm W2 (ms_mem msf)) (dxSA cx + 48) 4 (re_nheld e1 - 1)).
  { refine (field_of_region Ef _ 22 (dxSA cx) _ _ _ _ _ 48 4%N (SOff 33 (-1)) (re_nheld e1 - 1) RSA _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B22.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E33 by lia.
      rewrite unsigned_lit_small by (clear - KNH HNH; lia). f_equal; lia.
    - clear - KNH HNH Hnlt. cbn [Z.of_N]. lia.
    - cbn. lia. }
  (* the slot is the last one: the store writes back the key's own address *)
  assert (VF2 : val_mem SEGS (arm W2 (ms_mem msf)) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1))).
  { rewrite <- (Z.add_0_r (re_hp e1 + 8 * Z.of_nat n)), KL.
    refine (field_of_region Ef _ 26 (re_hp e1 + 8 * Z.of_nat n) _ _ _ _ _ 0 8%N (SOff 36 0) (key_addr (gf_key e1 n))
      RSL _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B26.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E36 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - clear - Hk4096 Hkceil RQK1 C1. cbn [Z.of_N]. lia.
    - cbn. lia. }
  apply HN.
  apply (gf_main cx s1 D p q regs1 ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl jj n ly2 S2 W2
    (ms_mem msf) _ (ms_regs msf) HB HRL R23 Hnlt Hges Hjj Hidx HGSF HCORE HFUT).
  exact (gfr_post cx e1 n ly1 S1 W1 m1 md1 (ms_mem ms1) k1 ly2 S2 W2 mem2 md2 (ms_mem msf) _ regs1 (ms_regs msf) l1 l2
    HAR1 HAR2 HGin1 HGle HSAle HHin ltac:(rewrite RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia) Kkb KR1 KR2 Hkept2
    HGr1 HGr2 Hpres2 Herr2 HJ2 Hfr2 Ebl1 Ebl2 Hmle2 HPR VF1 VF2).
- pose proof (gfr_entryL W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1) (Z.of_nat n)
    (key_addr (gf_lastkey e1)) (key_addr (gf_key e1 n)) Usp ltac:(rewrite WF; clear - Hsp0; lia)
    ltac:(rewrite WF; clear - Hsp0; lia) Hsp16 R21 R22 R20 R26 R19 HSAlo HSAhi Hh4096
    (gfr_mod16_8 _ Hh16)
    (Nat2Z.is_nonneg n) ltac:(rewrite HNH; clear - Hnlt HnL; lia) ltac:(clear - KNH; lia)
    ltac:(rewrite HNH in Hkh |- *; clear - Hkh Hhceil; lia) HDSH
    ltac:(clear - Hk4096 Hkceil RQK1; lia) ltac:(clear - Hl4096 Hlceil RQL1; lia)
    V8 V72 F96 F128 VH40 VH48 VS VL HW1 HW2) as HS.
  rewrite <- HE in HS. clear HE.
  assert (SHOK : sh_ok SEGS gf_Bx gf_SHL E (mrestrict (w_H W1) m1)).
  { unfold sh_ok, gf_SHL. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (gfr_shent E ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR1 HHin UBx U26);
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent E ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) 34 _ (-8) 0 HAR1 HHin UBx U34);
        rewrite ?RQH; rewrite HNH in Hkh; rewrite ?HNH; clear - Hkh Hnlt; lia.
    - apply (gfr_shent E ly1 S1 W1 m1 md1 (dxG cx) ATABLE 22 _ 40 52 HAR1 HGin1 UBx U22);
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  (* ---- run 1: the shadow check of &s->held[n], a0 = s->held[n], the jal to free ---- *)
  paj_run_tok RUN HS HJ SHOK gf_Bspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26 in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk cx ly1 S1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HGr1. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  assert (KR1 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W1) (ms_mem ms1) aa = aview SEGS (w_H W1) m1 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22, ?B26; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Bsp).
  destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
  assert (Has : ASTACK = 16384) by reflexivity.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* ---- free(s->held[n]) through the allocator's site rule, on the inner journal ---- *)
  eapply SRr_bind.
  { rewrite (pal_free B TL).
    eapply (AFREE W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS
      (dxmd cx) [] ly1 S1 _ k1 (key_addr (gf_key e1 n)) (Z.of_nat (length (key_text (gf_key e1 n))) + 1)
      (- DRAIN_FRAME) _ [] HJi Kkb).
    - rewrite Q10, E36. reflexivity.
    - rewrite Usp1. lia.
    - rewrite WF. reflexivity.
    - rewrite WF. lia.
    - rewrite Has, WS, WF. lia.
    - rewrite Q3, E3, R3. exact Hgp.
    - rewrite Q4, E4, R4. exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HGSB as (HG1 & HG2 & _).
      assert (HD8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] (ms_regs ms1)).
      + apply achain_low. clear - HD8 HG2 C1. unfold ASRC in *. lia.
      + rewrite Usp1, WF. clear - Hsp0. lia.
      + unfold s0Z. rewrite Q8, E8. unfold w64. apply unsigned_lit_small. clear - HD8 HG2. unfold ASRC in *. lia.
      + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
    - intros Hin0 i Hi.
      exact (gfr_fp cx ly1 S1 W1 m1 md1 e1 h1 _ out1 _ _ HAR1 HPERM HPERM0 HKae ltac:(lia) Hin0 i Hi).
    - exact HMOKF. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (l1 & l2 & Ebl1 & Ebl2) & Hfr2 &
    Hkept2 & Hmle2 & Herr2 & Hpres2).
  pose proof (proj1 HJ2i) as HAR2.
  assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)).
  { pose proof HGin1 as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HAEG _ HKae (eq_sym Heq))). }
  assert (HHin2 : In (re_hp e1, re_kh e1) (ablocks B ly2 S2)).
  { pose proof HHin as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HKH (eq_sym Heq))). }
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_stack_aj; [exact Hkept2 | exact HJ2i | exact Bsp | ..]; rewrite ?WS, ?WF; lia.
    - apply (gfr_kept_blk E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 md2 22 40 52 48 52 _ (dxG cx) ATABLE (dxSA cx)
        Hkept2 HAR2 HGin2 B22 HGin1); rewrite ?RQT;
        [clear - HGle HSAle; unfold AENT, ATABLE in *; lia | clear - HGle HSAle; unfold AENT, ATABLE in *; lia
        | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DGK; lia].
    - apply (gfr_kept_blk E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 md2 26 0 8 0 8 _ (re_hp e1) (re_kh e1)
        (re_hp e1 + 8 * Z.of_nat n) Hkept2 HAR2 HHin2 B26 HHin); rewrite ?RQH;
        [lia | rewrite HNH in Hkh; clear - Hkh Hnlt; lia | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DHK; lia].
    - apply (gfr_kept_blk E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 md2 34 (-8) 0 0 0 _ (re_hp e1) (re_kh e1)
        (re_hp e1 + 8 * re_nheld e1) Hkept2 HAR2 HHin2 B34 HHin); rewrite ?RQH;
        [rewrite HNH; clear - Hnlt; lia | clear - Hkh; lia | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DHK; lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall mm, (mm < 48)%nat -> ew Ea mm = ew E mm)
    by (intros mm Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  clear HEa.
  assert (UEa : forall k, (k < 48)%nat -> U Ea (SOff k 0) = U E (SOff k 0))
    by (intros k Hk; rewrite !U_SOff, (OLDa k Hk); reflexivity).
  assert (B22a : bv_unsigned (ew Ea 22) = dxSA cx) by (rewrite OLDa by lia; exact B22).
  assert (B26a : bv_unsigned (ew Ea 26) = re_hp e1 + 8 * Z.of_nat n) by (rewrite OLDa by lia; exact B26).
  assert (HJ2 : @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1)).
  { apply (ajournal_gx_pack SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
      (dxmem cx) (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1) memS);
      [exact HSTK1 | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | intros aa Haa; lia]. }
  assert (UBxa : U Ea gf_Bx = SHADOW_OFF) by (unfold gf_Bx in *; rewrite UEa by lia; exact UBx).
  assert (SHOK2 : sh_ok SEGS gf_Bx gf_SHL Ea (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, gf_SHL. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (gfr_shent Ea ly2 S2 W2 mem2 md2 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR2 HHin2 UBxa
        ltac:(rewrite UEa by lia; exact U26));
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent Ea ly2 S2 W2 mem2 md2 (re_hp e1) (re_kh e1) 34 _ (-8) 0 HAR2 HHin2 UBxa
        ltac:(rewrite UEa by lia; exact U34));
        rewrite ?RQH; rewrite HNH in Hkh; rewrite ?HNH; clear - Hkh Hnlt; lia.
    - apply (gfr_shent Ea ly2 S2 W2 mem2 md2 (dxG cx) ATABLE 22 _ 40 52 HAR2 HGin2 UBxa
        ltac:(rewrite UEa by lia; exact U22));
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  (* ---- run 2: the two shadow checks, s->nheld -= 1, s->held[n] = s->held[nheld - 1], j DLN ---- *)
  paj_run_to_tok RUNTO HS HJ2 SHOK2 gf_Bspan A_dr_next.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22a in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26a in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk cx ly1 S1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin2).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_nil. }
  rename HFr into HFr2, HG0 into HGr2. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  assert (KR2 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W2) (ms_mem msf) aa = aview SEGS (w_H W2) mem2 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msf) HFr2 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22a, ?B26a; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (20%bv : bv 5) F20.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26.
  prreg HS (27%bv : bv 5) F27.
  (* s3 keeps the symbolic value it entered with, the shadow address of &s->held[n] *)
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ev ss ms 19%bv HS) as F19;
    let e := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in change (sr_get (ss_regs ss) 19%bv) with e in F19;
    set (Ef := Ev) in HS, F19 end.
  cbn [ms_regs restrict mkst] in F19.
  assert (UF : forall mm, (mm < 512)%nat -> ew Ef mm = ew Ea mm)
    by (intros mm Hm; subst Ef; rewrite !ew_ewset_other by lia; reflexivity).
  assert (HPR : aregs_preserved regs1 (ms_regs msf)).
  { apply aregs_preserved_eqs.
    - rewrite F2, OLDa by lia. exact (EA 2%nat ltac:(lia)).
    - rewrite F3, OLDa by lia. exact (EA 3%nat ltac:(lia)).
    - rewrite F4, OLDa by lia. exact (EA 4%nat ltac:(lia)).
    - rewrite F8, OLDa by lia. exact (EA 8%nat ltac:(lia)).
    - rewrite F9, OLDa by lia. exact (EA 9%nat ltac:(lia)).
    - rewrite F18, OLDa by lia. exact (EA 18%nat ltac:(lia)).
    - rewrite F19, R19. apply gfr_den.
      assert (Ef26 : ew Ef 26 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite UF, OLDa by lia; exact E26).
      assert (Ef21 : ew Ef 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite UF, OLDa by lia; exact E21).
      pose proof (gfr_U_sh Ef 26 (re_hp e1 + 8 * Z.of_nat n) 0 Ef26 Ef21 Hr26 ltac:(rewrite Z.add_0_r; exact Hr26))
        as X.
      rewrite Z.add_0_r in X. exact X.
    - rewrite F20, OLDa by lia. exact (EA 20%nat ltac:(lia)).
    - rewrite F21, OLDa by lia. exact (EA 21%nat ltac:(lia)).
    - rewrite F22, OLDa by lia. exact (EA 22%nat ltac:(lia)).
    - rewrite F23, OLDa by lia. exact (EA 23%nat ltac:(lia)).
    - rewrite F24, OLDa by lia. exact (EA 24%nat ltac:(lia)).
    - rewrite F25, OLDa by lia. exact (EA 25%nat ltac:(lia)).
    - rewrite F26, OLDa by lia. exact (EA 26%nat ltac:(lia)).
    - rewrite F27, OLDa by lia. exact (EA 27%nat ltac:(lia)). }
  (* the two cells the arm wrote, read off the final regions *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSA.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RSL.
  cbn [ms_mem restrict] in RSA, RSL.
  assert (VF1 : val_mem SEGS (arm W2 (ms_mem msf)) (dxSA cx + 48) 4 (re_nheld e1 - 1)).
  { refine (field_of_region Ef _ 22 (dxSA cx) _ _ _ _ _ 48 4%N (SOff 33 (-1)) (re_nheld e1 - 1) RSA _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B22.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E33 by lia.
      rewrite unsigned_lit_small by (clear - KNH HNH; lia). f_equal; lia.
    - clear - KNH HNH Hnlt. cbn [Z.of_N]. lia.
    - cbn. lia. }
  assert (VF2 : val_mem SEGS (arm W2 (ms_mem msf)) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1))).
  { rewrite <- (Z.add_0_r (re_hp e1 + 8 * Z.of_nat n)).
    refine (field_of_region Ef _ 26 (re_hp e1 + 8 * Z.of_nat n) _ _ _ _ _ 0 8%N (SOff 35 0) (key_addr (gf_lastkey e1))
      RSL _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B26.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E35 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - clear - Hl4096 Hlceil RQL1 C1. cbn [Z.of_N]. lia.
    - cbn. lia. }
  apply HN.
  apply (gf_main cx s1 D p q regs1 ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl jj n ly2 S2 W2
    (ms_mem msf) _ (ms_regs msf) HB HRL R23 Hnlt Hges Hjj Hidx HGSF HCORE HFUT).
  exact (gfr_post cx e1 n ly1 S1 W1 m1 md1 (ms_mem ms1) k1 ly2 S2 W2 mem2 md2 (ms_mem msf) _ regs1 (ms_regs msf) l1 l2
    HAR1 HAR2 HGin1 HGle HSAle HHin ltac:(rewrite RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia) Kkb KR1 KR2 Hkept2
    HGr1 HGr2 Hpres2 Herr2 HJ2 Hfr2 Ebl1 Ebl2 Hmle2 HPR VF1 VF2).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice D, 2026-10-30): the GS-FREE arm over W_drain_cx_x.v's Section
   variables (B PST ARx MT RP MMAX RG), proving W_drain_gs.v's twin gs_free_stmt_x, with the entry's ghost list Hp and
   budget kr after cx and the cut's own ghost list Hp1 after S1, as W_drain_cx_x.v threads them.  Everything above
   this line is unchanged; the twin only adds names (the AR name with _x).
   - The AR-free names of Section c above (gf_entry, gf_key, gf_lastkey, GFEXC, the byte, entry, key-array and model
     lemmas gf_* / gsf_*, the auxiliaries gm_* that name no AR, and the run lemmas gfr_U_*, gfr_den*, gfr_entryL /
     gfr_entryE, gfr_mod16_8, gfr_not_wrange, gfr_in_rm, gfr_apresent_grows) are CITED, with the Section c variables
     and hypotheses each one abstracts (RG and HGSB for most of them).
   - The twins over ARx: GFPOST_x (the arm's post, with the free rule's room rp_RM at the budget kr2 the cut after the
     arm owes), gm_sep_head_x, gf_main_x, gfr_dup_x, gfr_dup_in_x, gfr_shent_x (W_journal_x.v's
     range_addressable_of_block_hp0_x), gfr_fp_x, gfr_awr_blk_x, gfr_kept_blk_x, gfr_post_x and the arm gs_free_x.
     Three kit lemmas the AR proof cites have no kit twin on this base and are restated over ARx with their proofs:
     YCbq.v's sep_blocks_pos / sep_blocks_perm (from the law alx_sep) and region_kept_stack_aj
     (W_LLVMFuzzerTestOneInput_pro_x.v:320's text).
   - The one allocator call, free #2 at 0x8394c, is AFREE in its caller-context form (W_journal_x.v
     afree_cf_rule_c_x), its return address 0x83950 in CTX_F (HCTX_fr2), its stack room W_journal_x.aj_stack_room_x.
     The room round (lib/A/W_drain_room_x.v): the cut owes seen_tr's RFree (|x| + 1) first (gsf_fut, from
     W_drain_gs.v gs_seen_end_old); gs_rm_take gives the rule's room 1 + (MT_rk's charge of the rest + kr) and the
     rule's post the room of the rest; gs_cnt_call gives the count premise and gs_cnt_free the counts after the call
     on the rule post's split, whose block size |key| + 1 is the event's |x| + 1 (gf_keylen). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x.
(* the room round's bookkeeping at an allocator call, the drain stages' one text *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_room_x.
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
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* W_drain_cx_x.v's Section c hypotheses this arm uses, in that file's order and text *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
(* the free rule in its caller-context form over the generic journal (W_journal_x.v Section hc), and the one call
   site of this arm (drain = 0x830dc; jal free 0x8394c) *)
Variable CTX_F : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0x874] CTX_F.   (* free #2 returns to 0x83950 *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].

(* ---- Kit lemmas over ARx that the kit has no twin of on this base. ---- *)
(* YCbq.v:713 sep_blocks_pos, from the separation law alx_sep *)
Lemma sep_blocks_pos_x : forall ly S Hp (W : world SEGS) mem md x y l1 l2 l3,
ARx ly S Hp W mem md -> ablocks B ly S = l1 ++ x :: l2 ++ y :: l3 -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l1 l2 l3 HAR E.
destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [Hq _].
rewrite E, !map_app in Hq. cbn in Hq. rewrite map_app in Hq. cbn in Hq.
exact (pairwise_In2 zdisjoint _ _ _ _ _ _ Hq eq_refl).
Qed.

(* YCbq.v:2587 sep_blocks_perm *)
Lemma sep_blocks_perm_x : forall ly S Hp (W : world SEGS) mem md x y l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: y :: l) -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l HAR HP.
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
apply in_split in Hx as (a1 & a2 & E1).
assert (HP2 : Permutation (a1 ++ a2) (y :: l)).
{ apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ a1 a2 x). rewrite <- E1. apply Permutation_sym. exact HP. }
assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & E2).
- pose proof (sep_blocks_pos_x ly S Hp W mem md y x b1 b2 a2 HAR ltac:(rewrite E1, E2, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint in *. lia.
- exact (sep_blocks_pos_x ly S Hp W mem md x y a1 b1 b2 HAR ltac:(rewrite E1, E2; reflexivity)).
Qed.

(* ---- What the arm's run leaves (GFPOST over ARx): the journal at the entry's Hp and the cut's Hp2, and the free
   rule's room rp_RM at the budget kr2 that the cut after the arm owes. ---- *)
Definition GFPOST_x (cx : dcx) (Hp : list Z) (e1 : rentry) (n : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (k1 : Z)
(ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (m2 : word -> option byte) (md2 : Model)
(regs1 regs2 : bvmap 5 word) (kr2 : nat) : Prop :=
aregs_preserved regs1 regs2 /\
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 (k1 + 1) /\
frames S2 = frames S1 /\
(exists l1 l2,
   ablocks B ly1 S1 =
     l1 ++ (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: l2 /\
   ablocks B ly2 S2 = l1 ++ l2) /\
mo_le MT S1 S2 (mo_free MT) /\
rp_RM RP S2 kr2 /\
(forall b m i, In (b, m) (ablocks B ly1 S1) -> 0 <= i < req_size m -> ~ GFEXC cx e1 n (b + i) ->
   aview SEGS (w_H W2) m2 (b + i) = aview SEGS (w_H W1) m1 (b + i)) /\
(forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
   ~ (as_errno B <= x < as_errno B + 4) ->
   aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 ->
   ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 ->
   ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x) /\
apres_kept B W1 m1 W2 m2 /\
(forall i, 0 <= i < 4 ->
   aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) /\
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1 - 1) /\
val_mem SEGS (arm W2 m2) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1)).

(* two blocks at distinct places of a permutation of the live blocks are apart *)
Lemma gm_sep_head_x : forall ly S Hp (W : world SEGS) m md x L y,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm_x ly S Hp W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

Ltac gm_cs_x := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

(* ---- The run's lemmas over ARx. ---- *)
(* a block pair of a live state occurs at most once in it *)
Lemma gfr_dup_x : forall ly S Hp (W : world SEGS) mem md x l1 l2 l3,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (l1 ++ x :: l2 ++ x :: l3) -> 0 <= snd x -> False.
Proof.
intros ly S Hp W mem md x l1 l2 l3 HAR HP Hx.
assert (HP2 : Permutation (l1 ++ x :: l2 ++ x :: l3) (x :: x :: (l1 ++ l2) ++ l3)).
{ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite app_assoc. apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm_x ly S Hp W mem md x x _ HAR (Permutation_trans HP HP2)) as D.
destruct x as [b m]. unfold zdisjoint, block_rng in D. cbn [fst snd] in D, Hx.
pose proof (req_size_pos m Hx). lia.
Qed.

Lemma gfr_dup_in_x : forall ly S Hp (W : world SEGS) mem md L1 L2 x,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (L1 ++ x :: L2) -> In x L2 -> 0 <= snd x -> False.
Proof.
intros ly S Hp W mem md L1 L2 x HAR HP Hin Hx. apply in_split in Hin as (l2 & l3 & ->).
exact (gfr_dup_x ly S Hp W mem md x L1 l2 l3 HAR HP Hx).
Qed.

(* one shadow entry over a sub-range of a live block (its range addressable by W_journal_x.v's hp0 form) *)
Lemma gfr_shent_x : forall Ex ly S Hp (W : world SEGS) mem md b m (mt : nat) p lo hi,
ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> U Ex gf_Bx = SHADOW_OFF -> U Ex (SOff mt 0) = p ->
b <= p + lo -> lo <= hi -> p + hi <= b + req_size m ->
shent_ok SEGS gf_Bx Ex (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros Ex ly S Hp W mem md b m mt p lo hi HAR Hin HBx Hpp H1 H2 H3.
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4 & Hc & Happ & _).
eapply shent_ok_of_range.
- exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md b m (p + lo) (hi - lo) HAR Hin H1
    ltac:(lia)).
- exact HBx.
- exact Hpp.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.

(* A block of the relay entry that was live at drain's entry is in drain's footprint dFP. *)
Lemma gfr_fp_x : forall cx ly S Hp (W : world SEGS) mem md e h OC out b m,
ARx ly S Hp W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) (ablocks B (dxly cx) (dxS cx)) ->
forall i, 0 <= i < req_size m -> inFP (dFP cx) (b + i).
Proof.
intros cx ly S Hp W mem md e h OC out b m HAR HP1 HPE0 Hae Hm Hin0 i Hi.
apply (Permutation_in _ HPE0) in Hin0.
assert (HFP : In (b, m) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx)) ->
  inFP (dFP cx) (b + i)).
{ intros Hx. unfold dFP, dr_fp. exists (b, b + req_size m).
  split; [right; exact (in_map (fun b0 => (fst b0, fst b0 + req_size (snd b0))) _ (b, m) Hx)|].
  cbn [fst snd]. lia. }
destruct Hin0 as [Hg | Hin0].
- exfalso. rewrite Hg in HP1.
  exact (gfr_dup_in_x ly S Hp W mem md [] _ (b, m) HAR HP1 (in_or_app _ _ _ (or_introl Hae)) Hm).
- apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; right; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hx]; [apply HFP; apply in_or_app; right; apply in_or_app; right; exact Hx|].
  exfalso. apply in_split in Hae as (a1 & a2 & Ea). rewrite Ea, <- app_assoc in HP1.
  apply (gfr_dup_in_x ly S Hp W mem md ((dxG cx, ATABLE) :: a1) (a2 ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx)
    (b, m) HAR HP1); [|exact Hm].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hx.
Qed.

(* A byte of a block of the relay entry is one drain may write. *)
Lemma gfr_awr_blk_x : forall cx ly S Hp (W : world SEGS) mem md e h OC out b m blc lyq a,
ARx ly S Hp W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) blc -> b <= a < b + req_size m ->
awr_byte DRAIN_STK_x (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq [] a.
Proof.
intros cx ly S Hp W mem md e h OC out b m blc lyq a HAR HP1 HPE0 Hae Hm Hinc Ha.
assert (DZ : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec DZ (b, m) (ablocks B (dxly cx) (dxS cx))) as [Hin0 | Hnin0].
- right; left. split.
  + replace a with (b + (a - b)) by lia.
    apply (gfr_fp_x cx ly S Hp W mem md e h OC out b m HAR HP1 HPE0 Hae Hm Hin0). lia.
  + exists b, m. split; [exact Hinc | exact Ha].
- right; right; left. exists b, m. split; [exact Hinc|]. split; [exact Hnin0 | exact Ha].
Qed.

(* A region inside a block that survives a call keeps its bytes and the presence of its window. *)
Lemma gfr_kept_blk_x : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
  ly2 S2 Hp2 md2 n lo hi wlo whi cs b m base,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ARx ly2 S2 Hp2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = base -> In (b, m) (ablocks B lyc Sc) ->
b <= base + lo -> base + hi <= b + req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b <= a < b + req_size m -> ~ Er a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er ly2 S2 Hp2 md2 n lo hi wlo whi cs b m base (_ & K2 & _) HAR2 Hin2 Hn Hin
  H1 H2 H3 H4 HnE.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. apply HnE. lia.
- intros _. apply (apresent_writable SEGS). exact (proj1 (Hpres a ltac:(lia))).
Qed.


(* The pieces of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cf rules and every carrier or statement it names
   -> their R twins; every other token is the strict text's. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp W mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREER : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_F R.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].

(* YCbq.v:2602 region_kept_stack_aj over ajournal_x (W_LLVMFuzzerTestOneInput_pro_x.v:320's text and proof) *)
Lemma region_kept_stack_aj_xR : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
  ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
    (K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
  pose proof asan_consts as (C1 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply K1; lia.
  - intros _. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.
(* ---- What the arm's run leaves (GFPOST over ARx): the journal at the entry's Hp and the cut's Hp2, and the free
   rule's room rp_RM at the budget kr2 that the cut after the arm owes. ---- *)
Definition GFPOST_xR (cx : dcx) (Hp : list Z) (e1 : rentry) (n : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (k1 : Z)
(ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (m2 : word -> option byte) (md2 : Model)
(regs1 regs2 : bvmap 5 word) (kr2 : nat) : Prop :=
aregs_preserved regs1 regs2 /\
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 (k1 + 1) /\
frames S2 = frames S1 /\
(exists l1 l2,
   ablocks B ly1 S1 =
     l1 ++ (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: l2 /\
   ablocks B ly2 S2 = l1 ++ l2) /\
mo_le MT S1 S2 (mo_free MT) /\
rp_RM RP S2 kr2 /\
(forall b m i, In (b, m) (ablocks B ly1 S1) -> 0 <= i < req_size m -> ~ GFEXC cx e1 n (b + i) ->
   aview SEGS (w_H W2) m2 (b + i) = aview SEGS (w_H W1) m1 (b + i)) /\
(forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
   ~ (as_errno B <= x < as_errno B + 4) ->
   aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 ->
   ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 ->
   ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x) /\
apres_kept B W1 m1 W2 m2 /\
(forall i, 0 <= i < 4 ->
   aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) /\
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1 - 1) /\
val_mem SEGS (arm W2 m2) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1)).
(* The cut the arm lands on, from the arm's post (gf_main over ARx): the room round's two conjuncts of dbud_x are
   the rule post's room (GFPOST_x at the budget of the rest of the trace) and the counts by gs_cnt_free. *)
Lemma gf_main_xR : forall cx Hp kr s1 D p q regs1 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent
  jb a o ha ks tl jj n ly2 S2 Hp2 (W2 : world SEGS) m2 md2 regs2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
(n < length (re_keys e1))%nat ->
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) ->
(13 < jj < q - p)%nat ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n ->
GSF s1 p q ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
GSfut cx s1 p q a jb o ha ks tl ->
GFPOST_xR cx Hp e1 n ly1 S1 W1 m1 k1 ly2 S2 Hp2 W2 m2 md2 regs1 regs2 (Z.to_nat (tr_cost MT_rk (List.tl tl)) + kr)%nat ->
DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2).
Proof.
intros cx Hp kr s1 D p q regs1 ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl jj n ly2 S2 Hp2 W2 m2 md2
  regs2 HB HRL R23 Hn Hge Hjj HI HF HCORE HFUT HPOST.
destruct HPOST as (HPR & HJ2 & HFR2 & (l1 & l2 & EB1 & EB2) & HMO & HRM2 & HKB & HKI & HKS & HPS & HAPK & HKE & VNH &
  VSL).
destruct HCORE as (HDMEM & HLINK & HSAME & HHIST & HRST & HBUD).
destruct HDMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT & HLIVE & HPERM).
cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no] in HOUT, HPERM, HLIVE.
destruct (gsf_line RG HGSB cx s1 p q jj n HF Hge HI) as (LP & _ & LSK & LBD & LPOS & LNO & LOC & LH & LKA).
destruct (gsf_fut RG HGSB cx s1 p q jj n a jb o ha ks tl HF Hge HI HFUT) as (tl2 & jb2 & Etl & HFUT2).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
assert (AR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (AR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _ & _ & HU & _ & _ & Hnh & HHP & _ & _ & HKEYS).
destruct HHP as [(Hz & Hk0) | (Hz & HinH & Hk1 & Hk2 & HgA)];
  [exfalso; rewrite Hk0 in Hn; cbn [length] in Hn; clear - Hn; lia|].
assert (Ez : (re_hp e1 =? 0) = false) by (apply Z.eqb_neq; exact Hz).
assert (RQH : req_size (re_kh e1) = re_kh e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0) as [E0|E0]; [exfalso; clear - Hk2 E0; lia | reflexivity]).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (HSLOT : re_hp e1 + 8 * Z.of_nat n + 8 <= re_hp e1 + re_kh e1)
  by (unfold re_nheld in Hk1; clear - Hk1 Hn; lia).
assert (HHP64 : 0 <= re_hp e1 < 2 ^ 64).
{ destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ AR1 HinH) as (_ & H4 & Hc & _). rewrite RQH in Hc.
  clear - H4 Hc HAC Hk2. lia. }
(* ---- the live blocks before and after the free ---- *)
match type of HPERM with Permutation _ (_ :: aentry_blks _ ++ ?r) => pose (Rbl := r) end.
pose (TB := (dxG cx, ATABLE)).
pose (HBk := (re_hp e1, re_kh e1)).
pose (BUF := if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]).
pose (KEYS2 := map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (swap_remove (0, [], []) n (re_keys e1))).
pose (X := BUF ++ KEYS2 ++ Rbl).
assert (EA2 : aentry_blks (gf_entry e1 n) = BUF ++ HBk :: KEYS2).
{ unfold aentry_blks, gf_entry. cbn [re_cap re_buf re_hp re_kh re_keys]. rewrite Ez. reflexivity. }
assert (P1 : Permutation (ablocks B ly1 S1)
  ((key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: TB :: aentry_blks (gf_entry e1 n) ++ Rbl)).
{ eapply Permutation_trans; [exact HPERM|].
  eapply Permutation_trans; [apply perm_skip; apply Permutation_app_tail; exact (gm_perm_entry e1 n Hn)|].
  cbn [app]. apply perm_swap. }
assert (P2 : Permutation (ablocks B ly2 S2) (TB :: aentry_blks (gf_entry e1 n) ++ Rbl)).
{ rewrite EB2.
  apply (Permutation_cons_inv (a := (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- EB1. exact P1. }
assert (PT : Permutation (ablocks B ly2 S2) (TB :: HBk :: X)).
{ eapply Permutation_trans; [exact P2|]. apply perm_skip. rewrite EA2, <- app_assoc. cbn [app].
  apply Permutation_sym, Permutation_middle. }
assert (PH : Permutation (ablocks B ly2 S2) (HBk :: TB :: X)) by exact (Permutation_trans PT (perm_swap HBk TB X)).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PT)); left; reflexivity).
assert (HB2 : In HBk (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PH)); left; reflexivity).
assert (X2 : forall b, In b X -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym PT)); right; right; exact Hb).
assert (SUB : forall b, In b (ablocks B ly2 S2) -> In b (ablocks B ly1 S1) /\
  zdisjoint (block_rng (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1)) (block_rng b)).
{ intros b Hb. rewrite EB2 in Hb. split.
  - rewrite EB1. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb].
  - apply (gm_sep_head_x ly1 S1 Hp1 W1 m1 md1 _ (l1 ++ l2));
      [exact AR1 | rewrite EB1; apply Permutation_sym, Permutation_middle | exact Hb]. }
assert (DTH : zdisjoint (block_rng TB) (block_rng HBk))
  by exact (gm_sep_head_x ly2 S2 Hp2 W2 m2 md2 TB (HBk :: X) HBk AR2 PT (or_introl eq_refl)).
assert (DTX : forall b, In b X -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (gm_sep_head_x ly2 S2 Hp2 W2 m2 md2 TB (HBk :: X) b AR2 PT (or_intror Hb))).
assert (DHX : forall b, In b X -> zdisjoint (block_rng HBk) (block_rng b))
  by (intros b Hb; exact (gm_sep_head_x ly2 S2 Hp2 W2 m2 md2 HBk (TB :: X) b AR2 PH (or_intror Hb))).
(* ---- what the arm keeps ---- *)
assert (VK : forall b x, In b (ablocks B ly2 S2) -> fst b <= x < fst b + req_size (snd b) ->
  ~ (dxSA cx + 48 <= x < dxSA cx + 52) -> ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros [pb mb] x Hb Hx H48 Hsl. destruct (SUB _ Hb) as (Hb1 & Hd). cbn [fst snd] in Hx.
  assert (Hi : 0 <= x - pb < req_size mb) by (clear - Hx; lia).
  pose proof (HKB pb mb (x - pb) Hb1 Hi) as E. replace (pb + (x - pb)) with x in E by ring.
  apply E. unfold GFEXC. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  intros [G1 | [G2 | G3]]; [clear - G1 Hd Hx; lia | exact (H48 G2) | exact (Hsl G3)]. }
assert (WK : forall b x, In b (ablocks B ly2 S2) -> fst b <= x < fst b + req_size (snd b) ->
  writable_at SEGS (arm W2 m2) x).
{ intros [pb mb] x Hb Hx. destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 pb mb AR2 Hb) as (_ & _ & _ & _ & Hpr & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (BK : forall b x, In b (ablocks B ly2 S2) -> fst b <= x < fst b + req_size (snd b) ->
  ~ (dxSA cx + 48 <= x < dxSA cx + 52) -> ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8) ->
  abyte_kept W1 m1 W2 m2 x).
{ intros b x Hb Hx H48 Hsl. split; [exact (VK b x Hb Hx H48 Hsl) | intros _; exact (WK b x Hb Hx)]. }
assert (KO : forall b x, In b X -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 x).
{ intros b x Hb Hx. apply (BK b x (X2 b Hb) Hx).
  - intros H48. pose proof (DTX b Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj. rewrite RQT in Dj.
    clear - Dj Hx H48 HGle HSAle. unfold AENT, ATABLE in *. lia.
  - intros Hs. pose proof (DHX b Hb) as Dj. unfold zdisjoint, block_rng, HBk in Dj. cbn [fst snd] in Dj. rewrite RQH in Dj.
    clear - Dj Hx Hs HSLOT. lia. }
assert (TK : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (dxSA cx + 48 <= x < dxSA cx + 52) ->
  abyte_kept W1 m1 W2 m2 x).
{ intros x Hx H48. apply (BK TB x TB2); [| exact H48 |].
  - unfold TB. cbn [fst snd]. rewrite RQT. clear - Hx HGle HSAle. unfold AENT, ATABLE in *. lia.
  - intros Hs. pose proof DTH as Dj. unfold zdisjoint, block_rng, TB, HBk in Dj. cbn [fst snd] in Dj. rewrite RQT, RQH in Dj.
    clear - Dj Hx Hs HSLOT HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (HK : forall x, re_hp e1 <= x < re_hp e1 + re_kh e1 ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8) -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx Hs. apply (BK HBk x HB2); [| | exact Hs].
  - unfold HBk. cbn [fst snd]. rewrite RQH. exact Hx.
  - intros H48. pose proof DTH as Dj. unfold zdisjoint, block_rng, TB, HBk in Dj. cbn [fst snd] in Dj. rewrite RQT, RQH in Dj.
    clear - Dj Hx H48 HGle HSAle. unfold AENT, ATABLE in *. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (EV : aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
  { replace x with (as_errno B + (x - as_errno B)) by ring. apply HKE. clear - Hx; lia. }
  split; [exact EV|]. intros _.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  apply (gm_img_wr RG); [exact (proj1 (HG x Hg)) | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [exact (conj (proj1 (HG x Hx)) (proj1 (proj2 (HG x Hx)))) | exact (conj (proj1 (HGO x Hx)) (proj1 (proj2 (HGO x Hx))))]).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by lia.
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  split; [exact (HKI x Hi Ho Hne)|].
  intros Hw. apply (gm_writable_kept (w_H W1) (w_H W2) m1 m2 x); [|exact Hw].
  intros Hpr. exact (HAPK x Hi Ho Hne Hpr). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
assert (FB : alloc_ceiling + DRAIN_STK_x <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
assert (FK2 : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (Hr : alloc_ceiling <= x < 2 ^ 64 /\ ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME))
    by (clear - Hx FB; unfold DRAIN_STK_x, DRAIN_STK, SL_STK, SL_FRAME, DRAIN_FRAME, ASTACK in *; lia).
  destruct Hr as [Hr1 Hr2].
  split; [exact (HKS x Hr1 Hr2)|]. intros Hw. apply (gm_writable_kept (w_H W1) (w_H W2) m1 m2 x); [|exact Hw].
  exact (HPS x Hr1 Hr2). }
(* ---- the registers ---- *)
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
{ intros r Hr. pose proof (HPR (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
assert (DR2 : dregs_line RG cx regs2 W2 m2).
{ apply (gm_dregs_kept RG HGSB cx regs1 regs2 W1 m1 W2 m2 HRL); try (apply PR; gm_cs_x). exact FK2. }
assert (E23 : getr regs2 23 = getr regs1 23) by (apply PR; gm_cs_x).
(* ---- the memory core ---- *)
assert (ROM2 : rom_view SEGS W2 m2).
{ intros x Hx. destruct (HROMO x Hx) as (_ & Hpin & Hne & _).
  destruct (Exists_dec (in_zr x) (as_owned_static B) (gm_in_zr_dec RG x)) as [Hown | Hno].
  - eapply (rom_pinned_view_x SEGS B ARx LAWS); [exact AR2 | exact (Hpin Hown)].
  - assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    rewrite (HKI x Hi Hno Hne). exact (HROM x Hx). }
assert (PK2 : apres_kept B (dxW cx) (dxmem cx) W2 m2)
  by (intros x Hi Ho He Hpr; exact (HAPK x Hi Ho He (HPRESK x Hi Ho He Hpr))).
assert (ENT2 : garr8 SEGS (arm W2 m2) (dxSA cx) (bzs (entry_bytes (gf_entry e1 n)))).
{ apply (gf_entry_after RG HGSB W1 m1 W2 m2 (dxSA cx) e1 n Hpad1 Hpad2 Hn HHP64 Hnh HENTB VNH).
  - intros x Hx. exact (proj1 (TK x ltac:(clear - Hx; unfold AENT; lia) ltac:(clear - Hx; lia))).
  - intros x Hx. exact (proj1 (TK x ltac:(clear - Hx; unfold AENT; lia) ltac:(clear - Hx; lia))). }
assert (AWR2 : awr W2 m2 (dxSA cx) AENT).
{ intros i Hi. apply (WK TB (dxSA cx + i) TB2). unfold TB. cbn [fst snd]. rewrite RQT.
  clear - Hi HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (OKX2 : aentry_okx B ly2 S2 W2 m2 (gf_entry e1 n)).
{ apply (gf_aentry_okx B RG HGSB ly1 S1 W1 m1 ly2 S2 W2 m2 e1 n HOKX Hn).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym P2)). right. apply in_or_app. left. exact Hb.
  - intros r Hr x Hx. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    + destruct (re_cap e1 =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
      pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & HBUF & _).
      destruct HBUF as [(Hc0 & _) | (Hcp & _ & HJk & _)]; [apply Z.eqb_neq in Ec; contradiction|].
      apply (KO (re_buf e1, re_cap e1) x).
      * apply in_or_app. left. unfold BUF. rewrite ?Ec. left. reflexivity.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        pose proof (req_size_pos (re_cap e1) ltac:(clear - Hcp; lia)) as (_ & RQ). clear - Hx HU HJk RQ. lia.
    + apply in_map_iff in Hr as (k & <- & Hk).
      apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
      * apply in_or_app. right. apply in_or_app. left. unfold KEYS2.
        apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        cbn [length] in Hx.
        pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & RQ). clear - Hx RQ. lia.
  - apply (gf_array_after RG HGSB W1 m1 W2 m2 (re_hp e1) (re_keys e1) n Hn); [| exact HgA | exact VSL |].
    + assert (Hin : In (nth (length (re_keys e1) - 1) (re_keys e1) (0, [], [])) (re_keys e1))
        by (apply nth_In; clear - Hn; lia).
      rewrite Forall_forall in HKEYS. destruct (HKEYS _ Hin) as (Hb & _).
      destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ AR1 Hb) as (_ & H4 & Hc & _).
      pose proof (req_size_pos (Z.of_nat (length (key_text (nth (length (re_keys e1) - 1) (re_keys e1) (0, [], [])))) + 1)
        ltac:(lia)) as (_ & RQ).
      clear - H4 Hc HAC RQ. lia.
    + intros x Hx Hs. exact (proj1 (HK x ltac:(unfold re_nheld in Hk1; clear - Hx Hk1; lia) Hs)). }
assert (SRC2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx.
    destruct (gm_src_fp B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. apply in_or_app. right. apply in_or_app. right. unfold Rbl. apply in_or_app. left.
      exact Hb.
  - intros b Hb. apply X2. apply in_or_app. right. apply in_or_app. right. unfold Rbl. apply in_or_app. left. exact Hb. }
assert (OTH2 : aothers_at RG W2 m2 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & V1 & V2 & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m2) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact V1] | split; [apply GV; [| | exact V2] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK2 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m2 x)
  by (intros x H1 H2; exact (gm_bk_trans _ _ W1 m1 W2 m2 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT2 : aout_at B RG ly2 S2 W2 m2 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct (gm_out_fp B RG _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, GSoc cx s1 p q) x).
    + apply in_or_app. right. apply in_or_app. right. unfold Rbl. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply X2. apply in_or_app. right. apply in_or_app. right. unfold Rbl. apply in_or_app. right.
    apply in_or_app. left. exact Hb. }
assert (DM2 : DMEM_xR B PST ARx RG R cx Hp ly2 S2 Hp2 W2 m2 md2 (k1 + 1) (gf_entry e1 n) h1
  (dvirt cx s1 false (swap_remove [] n (dlH cx s1 p)) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))
  out1 ev1 (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) LB1).
{ unfold DMEM_xR. cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no].
  refine (conj HJ2 (conj ROM2 (conj PK2 (conj (eq_trans HFR2 HFRM) (conj (gm_frame_kept RG HGSB cx W1 m1 W2 m2 FK2 HFRAME)
    (conj ENT2 (conj AWR2 (conj OKX2 (conj SRC2 (conj OTH2 (conj GSK2 (conj OUT2 (conj HLIVE _))))))))))))).
  exact P2. }
(* ---- the model ---- *)
assert (DL2 : DLINK (dvirt cx s1 false (swap_remove [] n (dlH cx s1 p)) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))
  (gf_entry e1 n) h1).
{ pose proof HLINK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  refine (conj K1 (conj K2 (conj K3 (conj _ (conj K5 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10 (conj K11 K12))))))))))).
  cbn [gf_entry re_keys dvirt drain_b_c.ds_H]. rewrite (gs_keys_texts_swap (re_keys e1) n Hn). f_equal. exact K4. }
pose proof (gsf_hist RG HGSB cx s1 D p q jj n h1 LB1 false false (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q)
  (GSoc cx s1 p q) (swap_remove [] n (dlH cx s1 p)) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q) HF Hge HI
  eq_refl eq_refl eq_refl eq_refl eq_refl (eq_sym LH) (eq_sym LKA) (eq_sym LNO) (eq_sym LOC) (eq_sym LSK) HHIST) as DH2.
rewrite LP in DH2.
(* C3: the key at slot n has the length of the model's held text at slot n, so the freed block is the trace's
   RFree (|x| + 1) *)
assert (HKL : Z.of_nat (length (key_text (gf_key e1 n))) = Z.of_nat (length (firstn jj (dline s1 p q)))).
{ pose proof HLINK as (_ & _ & _ & K4 & _). cbn [dvirt drain_b_c.ds_H] in K4.
  destruct (gs_index_lt _ _ _ HI) as (_ & Hnth). rewrite <- K4 in Hnth.
  exact (gf_keylen RG (re_keys e1) n _ Hn Hnth). }
assert (DB2 : dbud_x B MT RP MMAX cx kr ly2 S2 (spent + mo_free MT) tl2).
{ destruct HBUD as (HBUD0 & HRM1 & HCNT1). split; [|split].
  - pose proof HBUD0 as (Hle & Hsp & Hcost & Hlv & Hmax). rewrite Etl in Hcost, Hlv, Hmax.
    rewrite (proj1 (gm_tr_free MT RG _ _ _)) in Hcost. rewrite W_tr_peak.tr_peak_free in Hlv.
    rewrite (proj2 (proj2 (gm_tr_free MT RG _ _ _))) in Hmax.
    pose proof (mo_free_nonneg MT MTL) as Hf0.
    (* the free lowers the live bytes by exactly the key's block, the trace's RFree (|key| + 1), so the peak of the
       rest stays in room (W_tr_peak.v tr_peak_free) *)
    assert (BB : blocks_bytes S2 = blocks_bytes S1 - (Z.of_nat (length (key_text (gf_key e1 n))) + 1)).
    { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), EB1, EB2, !bsum_app, bsum_cons. cbn [snd]. lia. }
    split; [exact (mle_station MT (dxS cx) S1 S2 spent (mo_free MT) MTL Hle HMO)|].
    split; [lia|]. split; [lia|]. split; [lia | exact Hmax].
  - (* the room of the rest: the rule post's *)
    rewrite Etl in HRM2. exact HRM2.
  - (* the counts of the rest: the freed block leaves the split l1 ++ (p, |x| + 1) :: l2 *)
    rewrite Etl, EB1, HKL in HCNT1. rewrite EB2. exact (gs_cnt_free RP _ _ tl2 l1 l2 _ HCNT1). }
(* ---- the cut ---- *)
unfold DLN_xR.
exists regs2, ly2, S2, Hp2, m2, md2, (k1 + 1), (gf_entry e1 n), h1, out1, ev1, LB1, (spent + mo_free MT), jb2, a, o, ha,
  (swap_remove RelayRunF.adr0 n ks), tl2.
split; [reflexivity|].
split; [exact DR2|].
split; [cbn [gf_entry re_buf]; rewrite E23, R23; unfold w64; f_equal; lia|].
split; [exact LBD|].
split; [exact LPOS|].
split; [|exact HFUT2].
unfold DLC_xR, LCORE_xR. cbv zeta.
rewrite LP, LSK, LNO, LOC, LH, LKA.
exact (conj DM2 (conj DL2 (conj HSAME (conj DH2 (conj HRST DB2))))).
Qed.
(* The arm's post from its three steps: run 1, the free (with its post's room at kr2), run 2. *)
Lemma gfr_post_xR : forall cx Hp e1 n ly1 S1 Hp1 (W1 : world SEGS) m1 md1 mR1 k1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2'
  m2 md2 regs1 regs2 l1 l2 kr2,
ARx ly1 S1 Hp1 W1 m1 md1 -> ARx ly2 S2 Hp2 W2 mem2 md2' ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) -> dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE ->
In (re_hp e1, re_kh e1) (ablocks B ly1 S1) -> re_hp e1 + 8 * Z.of_nat n + 8 <= re_hp e1 + req_size (re_kh e1) ->
In (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) (ablocks B ly1 S1) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W1) mR1 aa = aview SEGS (w_H W1) m1 aa) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W2) m2 aa = aview SEGS (w_H W2) mem2 aa) ->
acall_kept SEGS B ly1 S1 W1 mR1 W2 mem2 (dsp0 cx + - DRAIN_FRAME - ASTACK) (dsp0 cx + - DRAIN_FRAME)
  (fun a => key_addr (gf_key e1 n) <= a <
     key_addr (gf_key e1 n) + req_size (Z.of_nat (length (key_text (gf_key e1 n))) + 1)) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) mR1) ->
mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) m2) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (key_addr (gf_key e1 n) <= a <
     key_addr (gf_key e1 n) + req_size (Z.of_nat (length (key_text (gf_key e1 n))) + 1)) ->
  apresent (w_H W1) mR1 a -> apresent (w_H W2) mem2 a) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) mR1 (as_errno B + i)) ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 (k1 + 1) ->
frames S2 = frames S1 ->
ablocks B ly1 S1 = l1 ++ (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: l2 ->
ablocks B ly2 S2 = l1 ++ l2 ->
mo_le MT S1 S2 (mo_free MT) ->
rp_RM RP S2 kr2 ->
aregs_preserved regs1 regs2 ->
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1 - 1) ->
val_mem SEGS (arm W2 m2) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1)) ->
GFPOST_xR cx Hp e1 n ly1 S1 W1 m1 k1 ly2 S2 Hp2 W2 m2 md2 regs1 regs2 kr2.
Proof.
intros cx Hp e1 n ly1 S1 Hp1 W1 m1 md1 mR1 k1 ly2 S2 Hp2 W2 mem2 md2' m2 md2 regs1 regs2 l1 l2 kr2 HAR1 HAR2 HGin1
  HGle HSAle HHin Hslot Kkb KR1 KR2 (K1 & K2 & K3 & K4 & K5 & K6) HGr1 HGr2 Hpres2 Herr2 HJf Hfr2 Ebl1 Ebl2 Hmle2 HRM2
  HPR V1 V2.
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 HGin1) as (_ & HG4096 & HGceil & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 HHin) as (_ & Hh4096 & Hhceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
assert (WSA : forall x, dxSA cx + 48 <= x < dxSA cx + 52 -> dxG cx <= x < dxG cx + req_size ATABLE)
  by (intros x Hx; rewrite RQT; clear - Hx HGle HSAle; unfold AENT, ATABLE in *; lia).
assert (WSL : forall x, re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8 ->
  re_hp e1 <= x < re_hp e1 + req_size (re_kh e1)) by (intros x Hx; clear - Hx Hslot; lia).
assert (NIMG : forall x, in_img SEGS x ->
  ~ (dxSA cx + 48 <= x < dxSA cx + 52) /\ ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8)).
{ intros x Hx. split; intros Hw.
  - exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR1 HGin1 (WSA x Hw) Hx).
  - exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR1 HHin (WSL x Hw) Hx). }
unfold GFPOST_xR.
split; [exact HPR|]. split; [exact HJf|]. split; [exact Hfr2|].
split; [exists l1, l2; split; [exact Ebl1 | exact Ebl2]|]. split; [exact Hmle2|]. split; [exact HRM2|].
split.
{ intros b m i Hbm Hi Hex. unfold GFEXC in Hex.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hbm) as (_ & Hb4096 & Hbceil & _).
  assert (Hr : 0 <= b + i < 2 ^ 64) by (clear - Hb4096 Hbceil Hi C1; lia).
  rewrite (KR2 _ Hr (fun H => Hex (or_intror (or_introl H))) (fun H => Hex (or_intror (or_intror H)))).
  rewrite (K2 b m i Hbm Hi (fun H => Hex (or_introl H))).
  exact (KR1 _ Hr (fun H => Hex (or_intror (or_introl H))) (fun H => Hex (or_intror (or_intror H)))). }
split.
{ intros x Hi Hno Herr. destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64) by (pose proof (pa_segs_low x Hi); unfold kLowMemEnd in *; lia).
  rewrite (KR2 x Hr N1 N2), (K3 x Hi Hno Herr). exact (KR1 x Hr N1 N2). }
split.
{ intros x Hx Hns.
  assert (N1 : ~ (dxSA cx + 48 <= x < dxSA cx + 52)) by (clear - Hx HSAle HGceil; unfold AENT, ATABLE in *; lia).
  assert (N2 : ~ (re_hp e1 + 8 * Z.of_nat n <= x < re_hp e1 + 8 * Z.of_nat n + 8))
    by (clear - Hx Hslot Hhceil; lia).
  assert (Hr : 0 <= x < 2 ^ 64) by (clear - Hx C1; lia).
  rewrite (KR2 x Hr N1 N2), (K1 x Hx ltac:(clear - Hns; lia)). exact (KR1 x Hr N1 N2). }
split.
{ intros x Hx Hns Hpr.
  apply (gfr_apresent_grows _ _ _ _ HGr2). apply K5; [exact Hx | clear - Hns; lia |].
  exact (gfr_apresent_grows _ _ _ _ HGr1 Hpr). }
split.
{ intros x Hi Hno Herr Hpr.
  assert (Hnot : forall ly0 S0 Hq0 (W0 : world SEGS) m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 -> ~ aowned B ly0 S0 x)
    by (intros ly0 S0 Hq0 W0 m0 md0 HA Ho; apply Hno;
        exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 x HA Hi) Ho)).
  apply (gfr_apresent_grows _ _ _ _ HGr2).
  apply (Hpres2 x Hi (Hnot _ _ _ _ _ _ HAR1) (Hnot _ _ _ _ _ _ HAR2) Herr).
  - intros Hk. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR1 Kkb Hk Hi).
  - exact (gfr_apresent_grows _ _ _ _ HGr1 Hpr). }
split.
{ intros i Hi.
  assert (Hin : inG (G_DR B RG) (as_errno B + i)).
  { unfold inG. apply Exists_exists. exists (as_errno B, 4). split.
    - unfold G_DR, G_SL. cbn [In]. repeat first [left; reflexivity | right].
    - unfold in_zr. cbn [fst snd]. lia. }
  destruct (HG _ Hin) as (Hi2 & _). destruct (NIMG _ Hi2) as (N1 & N2).
  assert (Hr : 0 <= as_errno B + i < 2 ^ 64) by (pose proof (pa_segs_low _ Hi2); unfold kLowMemEnd in *; lia).
  rewrite (KR2 _ Hr N1 N2), (Herr2 i Hi). exact (KR1 _ Hr N1 N2). }
split; [exact V1 | exact V2].
Qed.
(* =========================================================================================================
   THE ARM over ARx.
   ========================================================================================================= *)
Theorem gs_free_xR : gs_free_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr s1 D p q W1 c1 HB HGF HN.
destruct HGF as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks &
  tl & jj & n & Hcfg & HRL & R23 & R24 & R19 & R26 & R20 & V8 & V72 & Hnlt & Hges & Hjj & Hidx & HGSF & HCORE & HFUT).
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRST & HBUD).
pose proof HDMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT & HLIVE & HPERM).
pose proof HRL as (Usp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR2 & V192 & V200 & V56 & V48 & V64).
pose proof HFR2 as (F208 & F96 & F128 & _).
pose proof HB as (HPRE & HSA10 & HGin0 & HGle & HSAle & HGARR0 & HAWR0 & HENT0 & HB9 & HB10 & HB11 & HB12 & HB13 &
  HB14 & HB15 & HB16 & HPERM0 & HB18 & HB19 & HB20 & HB21 & HB22 & HMOK & HRM0 & HCNT0).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp & Htp & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK_x = 16976) by reflexivity.
assert (WF : DRAIN_FRAME = 336) by reflexivity.
assert (Hsp0 : alloc_ceiling + 16976 <= dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - WS Hceil Hslo Hshi H47; lia).
assert (Hsp16 : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
  by (unfold dsp0; rewrite WF, Zminus_mod, Hal16; reflexivity).
(* the relay's table block *)
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGapp, HGpres.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in HGle; clear - HGle HG4096; lia).
assert (HSAhi : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; clear - HSAle HGceil; lia).
(* the relay entry and its held array *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KF).
assert (HNH : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
destruct KHP as [(_ & Hk0) | (Hhp0 & HHin & Hkh & Hkh8 & HGA)].
{ exfalso. rewrite Hk0 in Hnlt. cbn [length] in Hnlt. clear - Hnlt. lia. }
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 HHin) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _).
assert (RQH : req_size (re_kh e1) = re_kh e1) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
rewrite RQH in Hhceil, Hhapp, Hhpres.
assert (Hkin : In (gf_key e1 n) (re_keys e1)) by (unfold gf_key; apply nth_In; exact Hnlt).
assert (Hlin : In (gf_lastkey e1) (re_keys e1)) by (unfold gf_lastkey; apply nth_In; lia).
destruct (proj1 (Forall_forall _ _) KF _ Hkin) as (Kkb & Kkg & Kknz & Kklen).
destruct (proj1 (Forall_forall _ _) KF _ Hlin) as (Klb & Klg & Klnz & Kllen).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Kkb) as (Hk16 & Hk4096 & Hkceil & Hkapp & Hkpres & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Klb) as (_ & Hl4096 & Hlceil & _).
pose proof (req_size_pos (Z.of_nat (length (key_text (gf_key e1 n))) + 1) ltac:(lia)) as (RQK1 & RQK2).
pose proof (req_size_pos (Z.of_nat (length (key_text (gf_lastkey e1))) + 1) ltac:(lia)) as (RQL1 & RQL2).
(* the cells the state reads *)
assert (VH40 : val_mem SEGS (arm W1 m1) (dxSA cx + 40) 8 (re_hp e1))
  by (apply (gf_entry_hp RG HGSB W1 m1 _ e1 Kp1); [clear - Hh4096 Hhceil Hkh8 C1; lia | exact HENTB]).
assert (VH48 : val_mem SEGS (arm W1 m1) (dxSA cx + 48) 4 (re_nheld e1))
  by (apply (gf_entry_nheld RG HGSB W1 m1 _ e1 Kp1); [clear - KNH HNH; lia | exact HENTB]).
assert (VS : val_mem SEGS (arm W1 m1) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_key e1 n)))
  by (apply (gf_ptrs_slot RG HGSB W1 m1 (re_hp e1) (re_keys e1) n Hnlt);
      [change (nth n (re_keys e1) gf_k0) with (gf_key e1 n); clear - Hk4096 Hkceil RQK1 C1; lia | exact HGA]).
assert (VL : val_mem SEGS (arm W1 m1) (re_hp e1 + 8 * re_nheld e1 - 8) 8 (key_addr (gf_lastkey e1))).
{ replace (re_hp e1 + 8 * re_nheld e1 - 8) with (re_hp e1 + 8 * Z.of_nat (length (re_keys e1) - 1))
    by (rewrite HNH; clear - Hnlt; lia).
  apply (gf_ptrs_slot RG HGSB W1 m1 (re_hp e1) (re_keys e1) (length (re_keys e1) - 1) ltac:(clear - Hnlt; lia));
    [change (nth (length (re_keys e1) - 1) (re_keys e1) gf_k0) with (gf_lastkey e1); clear - Hl4096 Hlceil RQL1 C1; lia
    | exact HGA]. }
(* the table block and the held array are two different blocks *)
assert (HNEGH : (dxG cx, ATABLE) <> (re_hp e1, re_kh e1)).
{ intros Heq. apply (gfr_dup_in_x ly1 S1 Hp1 W1 m1 md1 [] _ (dxG cx, ATABLE) HAR1 HPERM);
    [|cbn [snd]; unfold ATABLE; lia].
  apply in_or_app. left. rewrite Heq. unfold aentry_blks. rewrite (proj2 (Z.eqb_neq _ _) Hhp0).
  apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 HGin1 HHin HNEGH) as DGH.
rewrite RQT, RQH in DGH. unfold zdisjoint in DGH. cbn [fst snd] in DGH.
assert (HDSH : dxSA cx + 52 <= re_hp e1 \/ re_hp e1 + 8 * re_nheld e1 <= dxSA cx + 40)
  by (unfold ATABLE, AENT in *; clear - DGH HGle HSAle Hkh; lia).
assert (HW1 : forall o, 48 <= o < 52 -> writable_at SEGS (arm W1 m1) (dxSA cx + o))
  by (intros oo Hoo; apply HAWR; unfold AENT; lia).
assert (HW2 : forall o, 0 <= o < 8 -> writable_at SEGS (arm W1 m1) (re_hp e1 + 8 * Z.of_nat n + o))
  by (intros oo Hoo; apply (apresent_writable SEGS);
      exact (proj1 (Hhpres (re_hp e1 + 8 * Z.of_nat n + oo) ltac:(rewrite HNH in Hkh; clear - Hkh Hnlt Hoo; lia)))).
(* the three blocks the arm touches: the table block, the held array and the freed key's text *)
assert (HHae : In (re_hp e1, re_kh e1) (aentry_blks e1)).
{ unfold aentry_blks. rewrite (proj2 (Z.eqb_neq _ _) Hhp0). apply in_or_app. right. apply in_or_app. left. left.
  reflexivity. }
assert (HKae : In (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) (aentry_blks e1)).
{ unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
  exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hkin). }
assert (HAEG : forall x, In x (aentry_blks e1) -> x <> (dxG cx, ATABLE)).
{ intros x Hx Heq. subst x. apply (gfr_dup_in_x ly1 S1 Hp1 W1 m1 md1 [] _ (dxG cx, ATABLE) HAR1 HPERM);
    [apply in_or_app; left; exact Hx | cbn [snd]; unfold ATABLE; lia]. }
assert (HKH : (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) <> (re_hp e1, re_kh e1)).
{ intros Heq. pose proof HPERM as HP'. unfold aentry_blks in HP'.
  rewrite (proj2 (Z.eqb_neq _ _) Hhp0), <- !app_assoc in HP'. cbn [app] in HP'.
  eapply (gfr_dup_in_x ly1 S1 Hp1 W1 m1 md1
    ((dxG cx, ATABLE) :: (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)])) _ (re_hp e1, re_kh e1) HAR1 HP').
  - apply in_or_app. left. rewrite <- Heq.
    exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hkin).
  - cbn [snd]. lia. }
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 HGin1 Kkb
  (fun Heq => HAEG _ HKae (eq_sym Heq))) as DGK.
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 HHin Kkb (fun Heq => HKH (eq_sym Heq))) as DHK.
rewrite RQT in DGK. rewrite RQH in DHK. unfold zdisjoint in DGK, DHK. cbn [fst snd] in DGK, DHK.
(* the free's budget: the trace still owed starts with this free *)
destruct (gsf_fut RG HGSB cx s1 p q jj n a jb o ha ks tl HGSF Hges Hidx HFUT) as (tl2 & jb2 & Etl & Hfut2).
pose proof HBUD as (HBUD0 & HRMc & HCNTc).
assert (HMOKF : mo_ok MT S1 (mo_free MT)).
{ destruct HBUD0 as (Hmle & Hsp00 & Hcost & Hbb & Hmax).
  assert (HTC2 : 0 <= tr_cost MT tl2).
  { (* every request still owed asks a nonnegative size (W_drain_tr.v): the six signs of the next round state
       dnext s1, four of them through the line loop at S q, the expected list's two from the cut's DLINK *)
    pose proof HRST as (_ & HJ1 & HCU & _). destruct HJ1 as (_ & _ & _ & HNZ).
    pose proof HLINK as (_ & _ & _ & _ & L5 & _ & _ & _ & _ & L10 & L11 & _).
    pose proof HHIST as (_ & _ & _ & _ & _ & D6 & _).
    cbn [dvirt drain_b_c.ds_ka drain_b_c.ds_en drain_b_c.ds_ecap drain_b_c.ds_no] in L5, L10, L11, D6.
    pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & HOC).
    cbn [dvirt drain_b_c.ds_ocap] in HOC.
    pose proof HB15 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hmx & HnoO & _).
    pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEXP & _).
    pose proof HEXP as (_ & _ & _ & _ & (HEn & _) & _).
    destruct (gsf_line RG HGSB cx s1 p q jj n HGSF Hges Hidx) as (_ & _ & _ & HdbS & _ & G1 & G2 & _ & G4).
    assert (Hka : 0 <= dlka cx s1 p)
      by (rewrite <- L5; unfold drain_b_c.ent_ka; destruct (re_hp e1 =? 0); clear - Hkh8; lia).
    assert (Hoc : 0 <= GSoc cx s1 p q) by (clear - HOC; destruct HOC as [(Hc0 & _) | (Hc0 & _)]; lia).
    assert (Hno : 0 <= GSno cx s1 p q) by (rewrite D6; clear - HnoO; lia).
    destruct (gs_dnext_signs_at cx s1 (S q) HNZ HdbS ltac:(clear - HCU; unfold ulen in HCU; lia)
      ltac:(rewrite G1; exact Hno) ltac:(rewrite G2; exact Hoc) ltac:(rewrite G4; exact Hka))
      as (S1c & S1o & S1n & S1k).
    assert (He : 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1)) by (rewrite <- L10; unfold hl_n; lia).
    assert (Hec : 0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1))
      by (rewrite <- L11; unfold hl_n in HEn; lia).
    pose proof (gs_dsfut_sizes cx _ a _ _ _ _ _ _ jb o ha ks tl ltac:(clear - Hmx; lia) Hoc S1c S1o S1n He Hec S1k
      HFUT) as Hsz.
    rewrite Etl in Hsz. apply Forall_inv_tail in Hsz. exact (gs_tr_cost_nonneg MT MTL tl2 Hsz). }
  apply (mok_station MT (dxS cx) S1 _ spent (mo_free MT) MTL HMOK Hmle (mo_free_nonneg MT MTL)).
  assert (TC : tr_cost MT tl = mo_free MT + tr_cost MT tl2) by (rewrite Etl; reflexivity).
  rewrite TC in Hcost. lia. }
(* the room round at the call: the rule's room (MT_rk charges the head RFree 1) and its count premise *)
assert (HRMF : rp_RM RP S1 (1 + (Z.to_nat (tr_cost MT_rk tl2) + kr))).
{ rewrite Etl in HRMc.
  refine (gs_rm_take RP S1
    [RelayRunT.RFree (Z.of_nat (length (firstn jj (dline s1 p q))) + 1) (nth n ks RelayRunF.adr0)] tl2 kr 1 _ HRMc).
  unfold tr_cost. cbn. lia. }
assert (HCNTF : cnt_ok RP (ablocks B ly1 S1)) by exact (gs_cnt_call RP tl _ HCNTc).
subst c1. unfold cfg_at.
remember (Eimg (Ereg regs1 (map (Z_to_bv 64) [re_hp e1; re_nheld e1; re_hp e1 + 8 * re_nheld e1;
  key_addr (gf_lastkey e1); key_addr (gf_key e1 n)]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs1 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E2 : ew E 2 = getr regs1 2) by exact (EA 2%nat ltac:(lia)).
assert (E3 : ew E 3 = getr regs1 3) by exact (EA 3%nat ltac:(lia)).
assert (E4 : ew E 4 = getr regs1 4) by exact (EA 4%nat ltac:(lia)).
assert (E8 : ew E 8 = w64 ((rg_s RG + 4) / 8)) by exact (eq_trans (EA 8%nat ltac:(lia)) R8).
assert (E22 : ew E 22 = w64 (dxSA cx)) by exact (eq_trans (EA 22%nat ltac:(lia)) R22).
assert (E21 : ew E 21 = w64 SHADOW_OFF) by exact (eq_trans (EA 21%nat ltac:(lia)) R21).
assert (E26 : ew E 26 = w64 (re_hp e1 + 8 * Z.of_nat n)) by exact (eq_trans (EA 26%nat ltac:(lia)) R26).
assert (E34 : ew E 34 = Z_to_bv 64 (re_hp e1 + 8 * re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E36 : ew E 36 = Z_to_bv 64 (key_addr (gf_key e1 n)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 (key_addr (gf_lastkey e1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Hr26 : 0 <= re_hp e1 + 8 * Z.of_nat n < 2 ^ 64)
  by (rewrite HNH in Hkh; clear - Hh4096 Hhceil Hkh Hnlt C1; lia).
assert (Bsp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Usp).
assert (B22 : bv_unsigned (ew E 22) = dxSA cx)
  by (rewrite E22; apply unsigned_lit_small; clear - HSAlo HSAhi C1; lia).
assert (B26 : bv_unsigned (ew E 26) = re_hp e1 + 8 * Z.of_nat n)
  by (rewrite E26; apply unsigned_lit_small; rewrite HNH in Hkh; clear - Hh4096 Hhceil Hkh Hnlt C1; lia).
assert (B34 : bv_unsigned (ew E 34) = re_hp e1 + 8 * re_nheld e1)
  by (rewrite E34; apply unsigned_lit_small; rewrite HNH in Hkh |- *; clear - Hh4096 Hhceil Hkh C1; lia).
assert (UBx : U E gf_Bx = SHADOW_OFF) by (unfold gf_Bx; apply (U_atom E 21 SHADOW_OFF E21); unfold SHADOW_OFF; lia).
assert (U22 : U E (SOff 22 0) = dxSA cx) by (rewrite U_SOff, B22, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (U26 : U E (SOff 26 0) = re_hp e1 + 8 * Z.of_nat n)
  by (rewrite U_SOff, B26, Z.add_0_r; apply zcanon_id; unfold M64; rewrite HNH in Hkh;
      clear - Hh4096 Hhceil Hkh Hnlt C1; lia).
assert (U34 : U E (SOff 34 0) = re_hp e1 + 8 * re_nheld e1)
  by (rewrite U_SOff, B34, Z.add_0_r; apply zcanon_id; unfold M64; rewrite HNH in Hkh |- *;
      clear - Hh4096 Hhceil Hkh C1; lia).
destruct (Nat.eq_dec n (length (re_keys e1) - 1)) as [HnE | HnL].
- (* ===== variant E: the held key IS the last slot (n = nheld - 1); three regions ===== *)
  assert (KL : gf_lastkey e1 = gf_key e1 n) by (unfold gf_lastkey, gf_key; rewrite <- HnE; reflexivity).
  pose proof (gfr_entryE RG HGSB W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1) (Z.of_nat n)
    (key_addr (gf_lastkey e1)) (key_addr (gf_key e1 n)) Usp ltac:(rewrite WF; clear - Hsp0; lia)
    ltac:(rewrite WF; clear - Hsp0; lia) Hsp16 R21 R22 R20 R26 R19 HSAlo HSAhi Hh4096
    (gfr_mod16_8 RG _ Hh16)
    (Nat2Z.is_nonneg n) ltac:(rewrite HNH; clear - Hnlt HnE; lia) ltac:(clear - KNH; lia)
    ltac:(rewrite HNH in Hkh |- *; clear - Hkh Hhceil; lia) HDSH
    ltac:(clear - Hk4096 Hkceil RQK1; lia) ltac:(clear - Hl4096 Hlceil RQL1 C1; lia)
    V8 V72 F96 F128 VH40 VH48 VS HW1 HW2) as HS.
  rewrite <- HE in HS. clear HE.
  assert (SHOK : sh_ok SEGS gf_Bx gf_SHE E (mrestrict (w_H W1) m1)).
  { unfold sh_ok, gf_SHE. constructor; [|constructor; [|constructor]].
    - apply (gfr_shent_x E ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR1 HHin UBx U26);
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent_x E ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE 22 _ 40 52 HAR1 HGin1 UBx U22);
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  paj_run_tok_xR RUNR HS HJ SHOK gf_Bspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26 in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk_x cx ly1 S1 Hp1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HGr1. clear HF.
  lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  assert (KR1 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W1) (ms_mem ms1) aa = aview SEGS (w_H W1) m1 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22, ?B26; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Bsp).
  destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
  assert (Has : ASTACK = 16384) by reflexivity.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  eapply (SRrG_bind SEGS R R_trans).
  { rewrite (pal_free B TL).
    eapply (AFREER W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) memS
      (dxmd cx) [] ly1 S1 Hp1 _ k1 (key_addr (gf_key e1 n)) (Z.of_nat (length (key_text (gf_key e1 n))) + 1)
      (- DRAIN_FRAME) _ [] (Z.to_nat (tr_cost MT_rk tl2) + kr)%nat HJi Kkb).
    - rewrite Q10, E36. reflexivity.
    - rewrite Usp1. lia.
    - rewrite WF. reflexivity.
    - rewrite WF. lia.
    - rewrite Has, WS, WF. lia.
    - (* the stack room below the call, from the inner journal *)
      apply (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (- DRAIN_FRAME) _ HJi);
        [rewrite Usp1; lia | rewrite Has, WS, WF; lia].
    - rewrite Q3, E3, R3. exact Hgp.
    - rewrite Q4, E4, R4. exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HGSB as (HG1 & HG2 & _).
      assert (HD8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] (ms_regs ms1)).
      + apply achain_low. clear - HD8 HG2 C1. unfold ASRC in *. lia.
      + rewrite Usp1, WF. clear - Hsp0. lia.
      + unfold s0Z. rewrite Q8, E8. unfold w64. apply unsigned_lit_small. clear - HD8 HG2. unfold ASRC in *. lia.
      + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
    - exact (RO_ARx _ _ _ _ _ _ (proj1 HJi)).
    - (* the caller-context fact: the chain is cut, so the trace is the return address alone (HCTX_fr2) *)
      unfold raZ. cbn [spine map]. rewrite Q1. rewrite unsigned_lit_small by (clear - HBASE; lia).
      match goal with |- In [?x] _ =>
        replace x with (BASE + AF_fr_drain + 0x874) by (try unfold AF_fr_drain; try unfold BASE; ring) end.
      exact HCTX_fr2.
    - exact HRMF.
    - exact HCNTF.
    - intros Hin0 i Hi.
      exact (gfr_fp_x cx ly1 S1 Hp1 W1 m1 md1 e1 h1 _ out1 _ _ HAR1 HPERM HPERM0 HKae ltac:(lia) Hin0 i Hi).
    - exact HMOKF. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (l1 & l2 & Ebl1 & Ebl2) &
    Hfr2 & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
  pose proof (proj1 HJ2i) as HAR2.
  assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)).
  { pose proof HGin1 as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HAEG _ HKae (eq_sym Heq))). }
  assert (HHin2 : In (re_hp e1, re_kh e1) (ablocks B ly2 S2)).
  { pose proof HHin as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HKH (eq_sym Heq))). }
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_stack_aj_xR; [exact Hkept2 | exact HJ2i | exact Bsp | ..]; rewrite ?WS, ?WF; lia.
    - apply (gfr_kept_blk_x E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 Hp2 md2 22 40 52 48 52 _ (dxG cx) ATABLE
        (dxSA cx) Hkept2 HAR2 HGin2 B22 HGin1); rewrite ?RQT;
        [clear - HGle HSAle; unfold AENT, ATABLE in *; lia | clear - HGle HSAle; unfold AENT, ATABLE in *; lia
        | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DGK; lia].
    - apply (gfr_kept_blk_x E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 Hp2 md2 26 0 8 0 8 _ (re_hp e1) (re_kh e1)
        (re_hp e1 + 8 * Z.of_nat n) Hkept2 HAR2 HHin2 B26 HHin); rewrite ?RQH;
        [lia | rewrite HNH in Hkh; clear - Hkh Hnlt; lia | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DHK; lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall mm, (mm < 48)%nat -> ew Ea mm = ew E mm)
    by (intros mm Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  clear HEa.
  assert (UEa : forall k, (k < 48)%nat -> U Ea (SOff k 0) = U E (SOff k 0))
    by (intros k Hk; rewrite !U_SOff, (OLDa k Hk); reflexivity).
  assert (B22a : bv_unsigned (ew Ea 22) = dxSA cx) by (rewrite OLDa by lia; exact B22).
  assert (B26a : bv_unsigned (ew Ea 26) = re_hp e1 + 8 * Z.of_nat n) by (rewrite OLDa by lia; exact B26).
  assert (HJ2 : @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1)).
  { apply (ajournal_gx_pack_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp
      (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1) memS);
      [exact HSTK1 | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | intros aa Haa; lia]. }
  assert (UBxa : U Ea gf_Bx = SHADOW_OFF) by (unfold gf_Bx in *; rewrite UEa by lia; exact UBx).
  assert (SHOK2 : sh_ok SEGS gf_Bx gf_SHE Ea (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, gf_SHE. constructor; [|constructor; [|constructor]].
    - apply (gfr_shent_x Ea ly2 S2 Hp2 W2 mem2 md2 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR2 HHin2 UBxa
        ltac:(rewrite UEa by lia; exact U26));
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent_x Ea ly2 S2 Hp2 W2 mem2 md2 (dxG cx) ATABLE 22 _ 40 52 HAR2 HGin2 UBxa
        ltac:(rewrite UEa by lia; exact U22));
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 gf_Bspan A_dr_next.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22a in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26a in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk_x cx ly1 S1 Hp1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin2).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_nil. }
  rename HFr into HFr2, HG0 into HGr2. clear HF.
  lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into msf end.
  assert (KR2 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W2) (ms_mem msf) aa = aview SEGS (w_H W2) mem2 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msf) HFr2 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22a, ?B26a; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (20%bv : bv 5) F20.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26.
  prreg HS (27%bv : bv 5) F27.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ev ss ms 19%bv HS) as F19;
    let e := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in change (sr_get (ss_regs ss) 19%bv) with e in F19;
    set (Ef := Ev) in HS, F19 end.
  cbn [ms_regs restrict mkst] in F19.
  assert (UF : forall mm, (mm < 512)%nat -> ew Ef mm = ew Ea mm)
    by (intros mm Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (HPR : aregs_preserved regs1 (ms_regs msf)).
  { apply aregs_preserved_eqs.
    - rewrite F2, OLDa by lia. exact (EA 2%nat ltac:(lia)).
    - rewrite F3, OLDa by lia. exact (EA 3%nat ltac:(lia)).
    - rewrite F4, OLDa by lia. exact (EA 4%nat ltac:(lia)).
    - rewrite F8, OLDa by lia. exact (EA 8%nat ltac:(lia)).
    - rewrite F9, OLDa by lia. exact (EA 9%nat ltac:(lia)).
    - rewrite F18, OLDa by lia. exact (EA 18%nat ltac:(lia)).
    - rewrite F19, R19. apply gfr_den.
      assert (Ef26 : ew Ef 26 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite UF, OLDa by lia; exact E26).
      assert (Ef21 : ew Ef 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite UF, OLDa by lia; exact E21).
      pose proof (gfr_U_sh RG Ef 26 (re_hp e1 + 8 * Z.of_nat n) 0 Ef26 Ef21 Hr26
        ltac:(rewrite Z.add_0_r; exact Hr26)) as X.
      rewrite Z.add_0_r in X. exact X.
    - rewrite F20, OLDa by lia. exact (EA 20%nat ltac:(lia)).
    - rewrite F21, OLDa by lia. exact (EA 21%nat ltac:(lia)).
    - rewrite F22, OLDa by lia. exact (EA 22%nat ltac:(lia)).
    - rewrite F23, OLDa by lia. exact (EA 23%nat ltac:(lia)).
    - rewrite F24, OLDa by lia. exact (EA 24%nat ltac:(lia)).
    - rewrite F25, OLDa by lia. exact (EA 25%nat ltac:(lia)).
    - rewrite F26, OLDa by lia. exact (EA 26%nat ltac:(lia)).
    - rewrite F27, OLDa by lia. exact (EA 27%nat ltac:(lia)). }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSA.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RSL.
  cbn [ms_mem restrict] in RSA, RSL.
  assert (VF1 : val_mem SEGS (arm W2 (ms_mem msf)) (dxSA cx + 48) 4 (re_nheld e1 - 1)).
  { refine (field_of_region Ef _ 22 (dxSA cx) _ _ _ _ _ 48 4%N (SOff 33 (-1)) (re_nheld e1 - 1) RSA _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B22.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E33 by lia.
      rewrite unsigned_lit_small by (clear - KNH HNH; lia). f_equal; lia.
    - clear - KNH HNH Hnlt. cbn [Z.of_N]. lia.
    - cbn. lia. }
  (* the slot is the last one: the store writes back the key's own address *)
  assert (VF2 : val_mem SEGS (arm W2 (ms_mem msf)) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1))).
  { rewrite <- (Z.add_0_r (re_hp e1 + 8 * Z.of_nat n)), KL.
    refine (field_of_region Ef _ 26 (re_hp e1 + 8 * Z.of_nat n) _ _ _ _ _ 0 8%N (SOff 36 0) (key_addr (gf_key e1 n))
      RSL _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B26.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E36 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - clear - Hk4096 Hkceil RQK1 C1. cbn [Z.of_N]. lia.
    - cbn. lia. }
  assert (HRM2' : rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (List.tl tl)) + kr)) by (rewrite Etl; exact HRM2).
  apply HN.
  apply (gf_main_xR cx Hp kr s1 D p q regs1 ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl jj n ly2 S2
    Hp2 W2 (ms_mem msf) _ (ms_regs msf) HB HRL R23 Hnlt Hges Hjj Hidx HGSF HCORE HFUT).
  exact (gfr_post_xR cx Hp e1 n ly1 S1 Hp1 W1 m1 md1 (ms_mem ms1) k1 ly2 S2 Hp2 W2 mem2 md2 (ms_mem msf) _ regs1
    (ms_regs msf) l1 l2 _ HAR1 HAR2 HGin1 HGle HSAle HHin ltac:(rewrite RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia)
    Kkb KR1 KR2 Hkept2 HGr1 HGr2 Hpres2 Herr2 HJ2 Hfr2 Ebl1 Ebl2 Hmle2 HRM2' HPR VF1 VF2).
- pose proof (gfr_entryL RG HGSB W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1) (Z.of_nat n)
    (key_addr (gf_lastkey e1)) (key_addr (gf_key e1 n)) Usp ltac:(rewrite WF; clear - Hsp0; lia)
    ltac:(rewrite WF; clear - Hsp0; lia) Hsp16 R21 R22 R20 R26 R19 HSAlo HSAhi Hh4096
    (gfr_mod16_8 RG _ Hh16)
    (Nat2Z.is_nonneg n) ltac:(rewrite HNH; clear - Hnlt HnL; lia) ltac:(clear - KNH; lia)
    ltac:(rewrite HNH in Hkh |- *; clear - Hkh Hhceil; lia) HDSH
    ltac:(clear - Hk4096 Hkceil RQK1; lia) ltac:(clear - Hl4096 Hlceil RQL1; lia)
    V8 V72 F96 F128 VH40 VH48 VS VL HW1 HW2) as HS.
  rewrite <- HE in HS. clear HE.
  assert (SHOK : sh_ok SEGS gf_Bx gf_SHL E (mrestrict (w_H W1) m1)).
  { unfold sh_ok, gf_SHL. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (gfr_shent_x E ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR1 HHin UBx U26);
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent_x E ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) 34 _ (-8) 0 HAR1 HHin UBx U34);
        rewrite ?RQH; rewrite HNH in Hkh; rewrite ?HNH; clear - Hkh Hnlt; lia.
    - apply (gfr_shent_x E ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE 22 _ 40 52 HAR1 HGin1 UBx U22);
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  (* ---- run 1: the shadow check of &s->held[n], a0 = s->held[n], the jal to free ---- *)
  paj_run_tok_xR RUNR HS HJ SHOK gf_Bspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26 in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk_x cx ly1 S1 Hp1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HGr1. clear HF.
  lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  assert (KR1 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W1) (ms_mem ms1) aa = aview SEGS (w_H W1) m1 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22, ?B26; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Bsp).
  destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
  assert (Has : ASTACK = 16384) by reflexivity.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* ---- free(s->held[n]) through the allocator's site rule, on the inner journal ---- *)
  eapply (SRrG_bind SEGS R R_trans).
  { rewrite (pal_free B TL).
    eapply (AFREER W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) memS
      (dxmd cx) [] ly1 S1 Hp1 _ k1 (key_addr (gf_key e1 n)) (Z.of_nat (length (key_text (gf_key e1 n))) + 1)
      (- DRAIN_FRAME) _ [] (Z.to_nat (tr_cost MT_rk tl2) + kr)%nat HJi Kkb).
    - rewrite Q10, E36. reflexivity.
    - rewrite Usp1. lia.
    - rewrite WF. reflexivity.
    - rewrite WF. lia.
    - rewrite Has, WS, WF. lia.
    - (* the stack room below the call, from the inner journal *)
      apply (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (- DRAIN_FRAME) _ HJi);
        [rewrite Usp1; lia | rewrite Has, WS, WF; lia].
    - rewrite Q3, E3, R3. exact Hgp.
    - rewrite Q4, E4, R4. exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HGSB as (HG1 & HG2 & _).
      assert (HD8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] (ms_regs ms1)).
      + apply achain_low. clear - HD8 HG2 C1. unfold ASRC in *. lia.
      + rewrite Usp1, WF. clear - Hsp0. lia.
      + unfold s0Z. rewrite Q8, E8. unfold w64. apply unsigned_lit_small. clear - HD8 HG2. unfold ASRC in *. lia.
      + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
    - exact (RO_ARx _ _ _ _ _ _ (proj1 HJi)).
    - (* the caller-context fact: the chain is cut, so the trace is the return address alone (HCTX_fr2) *)
      unfold raZ. cbn [spine map]. rewrite Q1. rewrite unsigned_lit_small by (clear - HBASE; lia).
      match goal with |- In [?x] _ =>
        replace x with (BASE + AF_fr_drain + 0x874) by (try unfold AF_fr_drain; try unfold BASE; ring) end.
      exact HCTX_fr2.
    - exact HRMF.
    - exact HCNTF.
    - intros Hin0 i Hi.
      exact (gfr_fp_x cx ly1 S1 Hp1 W1 m1 md1 e1 h1 _ out1 _ _ HAR1 HPERM HPERM0 HKae ltac:(lia) Hin0 i Hi).
    - exact HMOKF. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (l1 & l2 & Ebl1 & Ebl2) &
    Hfr2 & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
  pose proof (proj1 HJ2i) as HAR2.
  assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)).
  { pose proof HGin1 as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HAEG _ HKae (eq_sym Heq))). }
  assert (HHin2 : In (re_hp e1, re_kh e1) (ablocks B ly2 S2)).
  { pose proof HHin as X. rewrite Ebl1 in X. rewrite Ebl2.
    exact (gfr_in_rm _ _ _ _ X (fun Heq => HKH (eq_sym Heq))). }
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_stack_aj_xR; [exact Hkept2 | exact HJ2i | exact Bsp | ..]; rewrite ?WS, ?WF; lia.
    - apply (gfr_kept_blk_x E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 Hp2 md2 22 40 52 48 52 _ (dxG cx) ATABLE
        (dxSA cx) Hkept2 HAR2 HGin2 B22 HGin1); rewrite ?RQT;
        [clear - HGle HSAle; unfold AENT, ATABLE in *; lia | clear - HGle HSAle; unfold AENT, ATABLE in *; lia
        | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DGK; lia].
    - apply (gfr_kept_blk_x E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 Hp2 md2 26 0 8 0 8 _ (re_hp e1) (re_kh e1)
        (re_hp e1 + 8 * Z.of_nat n) Hkept2 HAR2 HHin2 B26 HHin); rewrite ?RQH;
        [lia | rewrite HNH in Hkh; clear - Hkh Hnlt; lia | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DHK; lia].
    - apply (gfr_kept_blk_x E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 Hp2 md2 34 (-8) 0 0 0 _ (re_hp e1) (re_kh e1)
        (re_hp e1 + 8 * re_nheld e1) Hkept2 HAR2 HHin2 B34 HHin); rewrite ?RQH;
        [rewrite HNH; clear - Hnlt; lia | clear - Hkh; lia | lia | lia | cbv beta; intros aa Haa Hk; clear - Haa Hk DHK; lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall mm, (mm < 48)%nat -> ew Ea mm = ew E mm)
    by (intros mm Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  clear HEa.
  assert (UEa : forall k, (k < 48)%nat -> U Ea (SOff k 0) = U E (SOff k 0))
    by (intros k Hk; rewrite !U_SOff, (OLDa k Hk); reflexivity).
  assert (B22a : bv_unsigned (ew Ea 22) = dxSA cx) by (rewrite OLDa by lia; exact B22).
  assert (B26a : bv_unsigned (ew Ea 26) = re_hp e1 + 8 * Z.of_nat n) by (rewrite OLDa by lia; exact B26).
  assert (HJ2 : @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1)).
  { apply (ajournal_gx_pack_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp
      (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1) memS);
      [exact HSTK1 | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | intros aa Haa; lia]. }
  assert (UBxa : U Ea gf_Bx = SHADOW_OFF) by (unfold gf_Bx in *; rewrite UEa by lia; exact UBx).
  assert (SHOK2 : sh_ok SEGS gf_Bx gf_SHL Ea (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, gf_SHL. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (gfr_shent_x Ea ly2 S2 Hp2 W2 mem2 md2 (re_hp e1) (re_kh e1) 26 _ 0 8 HAR2 HHin2 UBxa
        ltac:(rewrite UEa by lia; exact U26));
        rewrite ?RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia.
    - apply (gfr_shent_x Ea ly2 S2 Hp2 W2 mem2 md2 (re_hp e1) (re_kh e1) 34 _ (-8) 0 HAR2 HHin2 UBxa
        ltac:(rewrite UEa by lia; exact U34));
        rewrite ?RQH; rewrite HNH in Hkh; rewrite ?HNH; clear - Hkh Hnlt; lia.
    - apply (gfr_shent_x Ea ly2 S2 Hp2 W2 mem2 md2 (dxG cx) ATABLE 22 _ 40 52 HAR2 HGin2 UBxa
        ltac:(rewrite UEa by lia; exact U22));
        rewrite ?RQT; clear - HGle HSAle; unfold AENT, ATABLE in *; lia. }
  (* ---- run 2: the two shadow checks, s->nheld -= 1, s->held[n] = s->held[nheld - 1], j DLN ---- *)
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 gf_Bspan A_dr_next.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22a in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. clear - Ha HGle HSAle. unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B26a in Ha.
      left. split; [|lia].
      apply (gfr_awr_blk_x cx ly1 S1 Hp1 W1 m1 md1 e1 h1 _ out1 (re_hp e1) (re_kh e1) _ _ aa HAR1 HPERM HPERM0 HHae
        ltac:(lia) HHin2).
      rewrite RQH. rewrite HNH in Hkh. clear - Ha Hkh Hnlt. lia. }
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_nil. }
  rename HFr into HFr2, HG0 into HGr2. clear HF.
  lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into msf end.
  assert (KR2 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
    ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H W2) (ms_mem msf) aa = aview SEGS (w_H W2) mem2 aa).
  { intros aa Ha H1 H2. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msf) HFr2 aa Ha). apply gfr_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22a, ?B26a; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (20%bv : bv 5) F20.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26.
  prreg HS (27%bv : bv 5) F27.
  (* s3 keeps the symbolic value it entered with, the shadow address of &s->held[n] *)
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ev ss ms 19%bv HS) as F19;
    let e := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in change (sr_get (ss_regs ss) 19%bv) with e in F19;
    set (Ef := Ev) in HS, F19 end.
  cbn [ms_regs restrict mkst] in F19.
  assert (UF : forall mm, (mm < 512)%nat -> ew Ef mm = ew Ea mm)
    by (intros mm Hm; subst Ef; rewrite !ew_ewset_other by lia; reflexivity).
  assert (HPR : aregs_preserved regs1 (ms_regs msf)).
  { apply aregs_preserved_eqs.
    - rewrite F2, OLDa by lia. exact (EA 2%nat ltac:(lia)).
    - rewrite F3, OLDa by lia. exact (EA 3%nat ltac:(lia)).
    - rewrite F4, OLDa by lia. exact (EA 4%nat ltac:(lia)).
    - rewrite F8, OLDa by lia. exact (EA 8%nat ltac:(lia)).
    - rewrite F9, OLDa by lia. exact (EA 9%nat ltac:(lia)).
    - rewrite F18, OLDa by lia. exact (EA 18%nat ltac:(lia)).
    - rewrite F19, R19. apply gfr_den.
      assert (Ef26 : ew Ef 26 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite UF, OLDa by lia; exact E26).
      assert (Ef21 : ew Ef 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite UF, OLDa by lia; exact E21).
      pose proof (gfr_U_sh RG Ef 26 (re_hp e1 + 8 * Z.of_nat n) 0 Ef26 Ef21 Hr26
        ltac:(rewrite Z.add_0_r; exact Hr26)) as X.
      rewrite Z.add_0_r in X. exact X.
    - rewrite F20, OLDa by lia. exact (EA 20%nat ltac:(lia)).
    - rewrite F21, OLDa by lia. exact (EA 21%nat ltac:(lia)).
    - rewrite F22, OLDa by lia. exact (EA 22%nat ltac:(lia)).
    - rewrite F23, OLDa by lia. exact (EA 23%nat ltac:(lia)).
    - rewrite F24, OLDa by lia. exact (EA 24%nat ltac:(lia)).
    - rewrite F25, OLDa by lia. exact (EA 25%nat ltac:(lia)).
    - rewrite F26, OLDa by lia. exact (EA 26%nat ltac:(lia)).
    - rewrite F27, OLDa by lia. exact (EA 27%nat ltac:(lia)). }
  (* the two cells the arm wrote, read off the final regions *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSA.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RSL.
  cbn [ms_mem restrict] in RSA, RSL.
  assert (VF1 : val_mem SEGS (arm W2 (ms_mem msf)) (dxSA cx + 48) 4 (re_nheld e1 - 1)).
  { refine (field_of_region Ef _ 22 (dxSA cx) _ _ _ _ _ 48 4%N (SOff 33 (-1)) (re_nheld e1 - 1) RSA _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B22.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E33 by lia.
      rewrite unsigned_lit_small by (clear - KNH HNH; lia). f_equal; lia.
    - clear - KNH HNH Hnlt. cbn [Z.of_N]. lia.
    - cbn. lia. }
  assert (VF2 : val_mem SEGS (arm W2 (ms_mem msf)) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1))).
  { rewrite <- (Z.add_0_r (re_hp e1 + 8 * Z.of_nat n)).
    refine (field_of_region Ef _ 26 (re_hp e1 + 8 * Z.of_nat n) _ _ _ _ _ 0 8%N (SOff 35 0) (key_addr (gf_lastkey e1))
      RSL _ _ _ _ _).
    - rewrite UF, OLDa by lia. exact B26.
    - cbn [In]. repeat first [left; reflexivity | right].
    - cbn [sv_denot]. rewrite UF, OLDa, E35 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - clear - Hl4096 Hlceil RQL1 C1. cbn [Z.of_N]. lia.
    - cbn. lia. }
  assert (HRM2' : rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (List.tl tl)) + kr)) by (rewrite Etl; exact HRM2).
  apply HN.
  apply (gf_main_xR cx Hp kr s1 D p q regs1 ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl jj n ly2 S2
    Hp2 W2 (ms_mem msf) _ (ms_regs msf) HB HRL R23 Hnlt Hges Hjj Hidx HGSF HCORE HFUT).
  exact (gfr_post_xR cx Hp e1 n ly1 S1 Hp1 W1 m1 md1 (ms_mem ms1) k1 ly2 S2 Hp2 W2 mem2 md2 (ms_mem msf) _ regs1
    (ms_regs msf) l1 l2 _ HAR1 HAR2 HGin1 HGle HSAle HHin ltac:(rewrite RQH; rewrite HNH in Hkh; clear - Hkh Hnlt; lia)
    Kkb KR1 KR2 Hkept2 HGr1 HGr2 Hpres2 Herr2 HJ2 Hfr2 Ebl1 Ebl2 Hmle2 HRM2' HPR VF1 VF2).
Qed.
End wR.


(* YCbq.v:2602 region_kept_stack_aj over ajournal_x (W_LLVMFuzzerTestOneInput_pro_x.v:320's text and proof) *)
Lemma region_kept_stack_aj_x : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
  ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof. eapply (region_kept_stack_aj_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* The cut the arm lands on, from the arm's post (gf_main over ARx): the room round's two conjuncts of dbud_x are
   the rule post's room (GFPOST_x at the budget of the rest of the trace) and the counts by gs_cnt_free. *)
Lemma gf_main_x : forall cx Hp kr s1 D p q regs1 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent
  jb a o ha ks tl jj n ly2 S2 Hp2 (W2 : world SEGS) m2 md2 regs2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
(n < length (re_keys e1))%nat ->
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) ->
(13 < jj < q - p)%nat ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n ->
GSF s1 p q ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
GSfut cx s1 p q a jb o ha ks tl ->
GFPOST_x cx Hp e1 n ly1 S1 W1 m1 k1 ly2 S2 Hp2 W2 m2 md2 regs1 regs2 (Z.to_nat (tr_cost MT_rk (List.tl tl)) + kr)%nat ->
DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2).
Proof. eapply (gf_main_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* The arm's post from its three steps: run 1, the free (with its post's room at kr2), run 2. *)
Lemma gfr_post_x : forall cx Hp e1 n ly1 S1 Hp1 (W1 : world SEGS) m1 md1 mR1 k1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2'
  m2 md2 regs1 regs2 l1 l2 kr2,
ARx ly1 S1 Hp1 W1 m1 md1 -> ARx ly2 S2 Hp2 W2 mem2 md2' ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) -> dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE ->
In (re_hp e1, re_kh e1) (ablocks B ly1 S1) -> re_hp e1 + 8 * Z.of_nat n + 8 <= re_hp e1 + req_size (re_kh e1) ->
In (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) (ablocks B ly1 S1) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W1) mR1 aa = aview SEGS (w_H W1) m1 aa) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 48 <= aa < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= aa < re_hp e1 + 8 * Z.of_nat n + 8) ->
  aview SEGS (w_H W2) m2 aa = aview SEGS (w_H W2) mem2 aa) ->
acall_kept SEGS B ly1 S1 W1 mR1 W2 mem2 (dsp0 cx + - DRAIN_FRAME - ASTACK) (dsp0 cx + - DRAIN_FRAME)
  (fun a => key_addr (gf_key e1 n) <= a <
     key_addr (gf_key e1 n) + req_size (Z.of_nat (length (key_text (gf_key e1 n))) + 1)) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) mR1) ->
mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) m2) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (key_addr (gf_key e1 n) <= a <
     key_addr (gf_key e1 n) + req_size (Z.of_nat (length (key_text (gf_key e1 n))) + 1)) ->
  apresent (w_H W1) mR1 a -> apresent (w_H W2) mem2 a) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) mR1 (as_errno B + i)) ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 (k1 + 1) ->
frames S2 = frames S1 ->
ablocks B ly1 S1 = l1 ++ (key_addr (gf_key e1 n), Z.of_nat (length (key_text (gf_key e1 n))) + 1) :: l2 ->
ablocks B ly2 S2 = l1 ++ l2 ->
mo_le MT S1 S2 (mo_free MT) ->
rp_RM RP S2 kr2 ->
aregs_preserved regs1 regs2 ->
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1 - 1) ->
val_mem SEGS (arm W2 m2) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (gf_lastkey e1)) ->
GFPOST_x cx Hp e1 n ly1 S1 W1 m1 k1 ly2 S2 Hp2 W2 m2 md2 regs1 regs2 kr2.
Proof. eapply (gfr_post_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* =========================================================================================================
   THE ARM over ARx.
   ========================================================================================================= *)
Theorem gs_free_x : gs_free_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (gs_free_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | (apply afree_cf_rule_c_xR_of_x; assumption) | (apply arealloc_cf_rule_c_xR_of_x; assumption) | (intros; exact I) | assumption]. Qed.

End cx.
End bx.
End ax.
