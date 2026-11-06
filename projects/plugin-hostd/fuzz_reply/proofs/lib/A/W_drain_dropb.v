(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the NEXT segment of the ASan walk of fuzz_reply's drain (fuzz_reply.asan
   0x836f4 .. 0x83738 and the loop's exit edge to 0x83a4c), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and of this lane's W_has_prefix.v / W_send_line_loop.v.
   The statement is W_drain_cx.v's dr_next_stmt; the Section header below is that file's.

   relay.c:214-216: start = nul + 1; nul = memchr(start, 0, s->used - (start - s->buf)).  From the cut DLN
   (s7 = s->buf + p - 1) the walk checks the shadow of s->used and s->buf (both zero: the relay entry lies in the
   table block), loads s->buf and s->used, calls memchr #2 (0x8372c) through the shared amemchr_realizesM (AMEMCHR)
   and branches: a NUL at q = p + k goes back to the line loop's head DLL (0x836bc), none to DLR (0x83a4c).
   The model does not move: DLL / DLR carry DLN's core and future at the same p, with the memory after the call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_next.v, with its numbers changed; 1366 of its 1912 lines of code are new or changed and 1062 lines of the source are left out. *)
(* The DROPB half of the DROP segment of the ASan walk of fuzz_reply's drain (fuzz_reply.asan 0x83668 ..
   0x836bc / 0x83a4c): from the cut DDM (W_drain_dropb_cx.v, after the inlined list_drop) the `n < 0` and
   `n == 0` arms are refuted by the atom fact 1 <= n <= 16384, s->used += n is stored at 0x83684 (the relay
   table's block), memchr(s->buf, 0, s->used) is called at 0x836a4 (AMEMCHR, the shared amemchr_realizesM),
   192(sp) = (SA + 8) >> 3 is stored, and `beqz s7` at 0x836b8 picks the line loop's first cut: DLL with p = 0
   and q the first NUL (0x836bc), or DLR with p = 0 (0x83a4c, through 0x83a48 `mv s10, s8`).
   The relay entry DLL / DLR carry is W_drain_dropb_cx.v's dr_used e1 n.  Statement: dr_dropb_stmt. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_dropb_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- The symbolic state at DDM (0x83668). ----
   Atoms beyond the 32 registers: 32 = SA (the relay entry), 33 = s->buf, 34 = s->used.  s11 and s10 are
   pinned to SA + 24 and SA + 16; s5 is the shadow base's own atom 21 (Bx), s3 = n carries the fact 1 <= n <= 16384.
   The frame region holds the three slots the segment reads (208, 216, 224) and the write window of 192(sp); the
   relay entry's region holds s->buf and s->used with the write window of s->used; the shadow list covers
   [SA + 16, SA + 32), so both shadow fast checks fold to 0. *)
Definition dbBx : sv := SOff 21 0.
Definition DB_HI : Z := 140737479966720.
Definition db_regs : list sv := sr_set (sr_set sr_atoms 27%bv (SOff 32 24)) 26%bv (SOff 32 16).
Definition db_frame : YP09.region := YP09.mkRegion (Some 2%nat) 192 232 192 200
  [ YP09.mkChunk 208 (CVal 8 (SOff 32 8));
    YP09.mkChunk 216 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 16) (SLit 3)) (SOff 21 0)));
    YP09.mkChunk 224 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 24) (SLit 3)) (SOff 21 0))) ].
Definition db_ent : YP09.region := YP09.mkRegion (Some 32%nat) 16 32 24 32
  [ YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0)) ].
Definition db_regions : smem := [ db_frame; db_ent ].
Definition db_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF 1 16384 0); (21%nat, mkAF SB SB 0);
    (32%nat, mkAF 4096 DB_HI 0) ] [] [].
Definition ss_db : sstate := mkSS A_dr_join db_regs db_regions None db_facts.
Definition DB_SH : list shent := [ mkSHE 32 16 32 ].
Definition db_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition db_extra (SA BUF USED : Z) : list word := map (Z_to_bv 64) [SA; BUF; USED].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).


(* ---- Byte helpers. ---- *)
Lemma db_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma db_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma db_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.

Lemma db_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma db_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, db_nth_zle by exact Hk. rewrite db_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma db_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.

Lemma db_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.

Lemma db_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite db_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite db_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma db_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite db_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite db_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite db_le_byte1 by exact Hr. reflexivity.
Qed.

Lemma db_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Ltac db_len := rewrite ?length_app, ?db_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].

(* RelayRep.v entry_bytes: fd, eof, skip (4 each), pad1 (4), buf at + 16, used at + 24, cap, hp, nheld, pad2. *)
Lemma db_entry_buf : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_buf e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 16) 8 (re_buf e).
Proof.
intros W m SA e Hp1 Hb H.
unfold entry_bytes in H. rewrite !db_bzs_app, !app_assoc in H.
do 5 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (db_le8_bytes (re_buf e) Hb) in H.
apply (db_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hb|].
apply (db_garr8_at _ _ _ _ H). db_len. lia.
Qed.

Lemma db_entry_used : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_used e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 24) 8 (re_used e).
Proof.
intros W m SA e Hp1 Hb H.
unfold entry_bytes in H. rewrite !db_bzs_app, !app_assoc in H.
do 4 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (db_le8_bytes (re_used e) Hb) in H.
apply (db_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hb|].
apply (db_garr8_at _ _ _ _ H). db_len. lia.
Qed.

(* a byte of a garr8 run, as the ASan view reads it *)
Lemma db_garr8_aview : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j H Hj. unfold aview. pose proof (proj2 (H j Hj)) as Hr.
unfold arm in H. rewrite (garr8_mbyte SEGS (mrestrict (w_H W) m) base l j H Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma db_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.

(* the relay entry's bytes around its used field *)
Definition db_epre (e : rentry) : list byte :=
  Mem.le4 (Z_to_bv 64 (re_fd e)) ++ Mem.le4 (Z_to_bv 64 (re_eof e)) ++ Mem.le4 (Z_to_bv 64 (re_skip e)) ++
  re_pad1 e ++ Mem.le8 (Z_to_bv 64 (re_buf e)).
Definition db_epost (e : rentry) : list byte :=
  Mem.le8 (Z_to_bv 64 (re_cap e)) ++ Mem.le8 (Z_to_bv 64 (re_hp e)) ++ Mem.le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e.

Lemma db_entry_split : forall e, entry_bytes e = db_epre e ++ Mem.le8 (Z_to_bv 64 (re_used e)) ++ db_epost e.
Proof. intros e. unfold entry_bytes, db_epre, db_epost. rewrite <- !app_assoc. reflexivity. Qed.

Lemma db_epre_len : forall e, length (re_pad1 e) = 4%nat -> length (bzs (db_epre e)) = 24%nat.
Proof. intros e H. unfold db_epre. rewrite db_bzs_len. db_len. rewrite H. reflexivity. Qed.

Lemma db_epost_len : forall e, length (re_pad2 e) = 4%nat -> length (bzs (db_epost e)) = 24%nat.
Proof. intros e H. unfold db_epost. rewrite db_bzs_len. db_len. rewrite H. reflexivity. Qed.

(* s->used rewritten: the entry's bytes with the new used field *)
Lemma db_garr8_used : forall (W W' : world SEGS) m m' SA e u,
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
(forall x, SA <= x < SA + 56 -> ~ (SA + 24 <= x < SA + 32) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
0 <= u < 2 ^ 64 -> val_mem SEGS (arm W' m') (SA + 24) 8 u ->
garr8 SEGS (arm W' m') SA (bzs (db_epre e ++ Mem.le8 (Z_to_bv 64 u) ++ db_epost e)).
Proof.
intros W W' m m' SA e u H Hp1 Hp2 K Hu Hv.
rewrite db_entry_split, !db_bzs_app in H. rewrite !db_bzs_app.
apply garr8_app in H as [Hpre H]. apply garr8_app in H as [_ Hpost].
rewrite (db_epre_len e Hp1) in Hpost. rewrite db_bzs_len, Mem.length_le8 in Hpost.
apply garr8_app. split.
- apply (db_garr8_kept W m W' m' SA _ Hpre). intros x Hx. rewrite (db_epre_len e Hp1) in Hx. apply K; lia.
- apply garr8_app. split.
  + rewrite (db_epre_len e Hp1), (db_le8_bytes u Hu).
    apply (db_garr8_of_val W' m' _ 8 u); [change (8 * Z.of_nat 8) with 64; exact Hu|].
    replace (SA + Z.of_nat 24) with (SA + 24) by lia. exact Hv.
  + rewrite (db_epre_len e Hp1), db_bzs_len, Mem.length_le8.
    apply (db_garr8_kept W m W' m' _ _ Hpost). intros x Hx. rewrite (db_epost_len e Hp2) in Hx. apply K; lia.
Qed.

(* ---- Symbolic values. ---- *)
Lemma db_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma db_div8 : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 61.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Lemma db_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. pose proof (db_div8 (v + c) Hc). lia.
Qed.

Lemma db_U_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SB ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 21 0)) = SHADOW_OFF + (v + c) / 8.
Proof.
intros E n v c Hn H21 Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (db_U_srl E n v c Hn Hv Hc), (U_atom E 21 SB H21) by (unfold SB; lia).
pose proof (db_div8 (v + c) Hc) as Hd.
replace SB with SHADOW_OFF by reflexivity.
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma db_U_add : forall E i j u v, ew E i = Z_to_bv 64 u -> ew E j = Z_to_bv 64 v ->
0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u + v < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff i 0) (SOff j 0)) = u + v.
Proof.
intros E i j u v Hi Hj Hu Hv Huv. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E i u Hi Hu), (U_atom E j v Hj Hv). apply zcanon_id. unfold M64. lia.
Qed.

Lemma db_shadow_range : forall a, 0 <= a < 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64.
Proof. intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (db_div8 a ltac:(lia)). lia. Qed.

(* A register of a reached symbolic state, as the denotation of its symbolic value (not normalized). *)
Ltac db_rreg HS r Hr :=
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

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
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
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
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
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

Ltac db_in := repeat (first [left; reflexivity | right]).

(* ---- Where the cut's representations live: below the allocator ceiling and off the relay table's block. ----
   The segment writes s->used (in the table's block), 192(sp) and memchr's scratch below the frame; every byte
   the line loop's representations read lies in another live block or in the image band. *)
Definition db_out (G a : Z) : Prop := 0 <= a < alloc_ceiling /\ (a < G \/ G + 896 <= a).

Lemma db_blk_out : forall ly S (W : world SEGS) mem md G q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> zdisjoint (G, req_size ATABLE) (q, req_size n) ->
q <= a < q + req_size n -> db_out G a.
Proof.
intros ly S W mem md G q n a HAR Hin Hd Ha.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQ in Hd. unfold db_out. lia.
Qed.

Lemma db_img_out : forall G a lo hi, off_img G 896 -> 0x10000 <= lo -> lo <= a -> a < hi -> hi <= 0x5fb000 ->
db_out G a.
Proof. intros G a lo hi HGo H1 H2 H3 H4. pose proof asan_consts as (C1 & _). unfold off_img, db_out in *. lia. Qed.

Lemma db_G_out : forall ly S (W : world SEGS) mem md G a,
AR SEGS B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> inG (G_DR B RG) a -> db_out G a.
Proof.
intros ly S W mem md G a HAR HTB Ha.
pose proof (HG a Ha) as (Himg & _). pose proof (pa_segs_low a Himg) as Hl.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
unfold db_out. split; [lia|].
destruct (Z_lt_ge_dec a G) as [H1|H1]; [left; exact H1|].
destruct (Z_lt_ge_dec a (G + 896)) as [H2|H2]; [|right; lia].
assert (Hin2 : G <= a < G + req_size ATABLE) by (rewrite RQ; lia).
exfalso. apply (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR
  (or_introl (ex_intro _ G (ex_intro _ ATABLE (conj HTB Hin2)))))).
exact Himg.
Qed.

(* the relay table's block is apart from every other block the cut names *)
Lemma db_sep : forall ly S (W : world SEGS) mem md G rest b,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((G, ATABLE) :: rest) -> In b rest ->
zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b)).
Proof.
intros ly S W mem md G rest b HAR HP Hb.
apply in_split in Hb as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md (G, ATABLE) b (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

Lemma db_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma db_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma db_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma db_aentry_fp_out : forall ly S (W : world SEGS) mem md e G,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly S) /\ zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S W mem md e G HAR HE HB r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & HU8 & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct (HB (re_buf e, re_cap e) ltac:(unfold aentry_blks; rewrite Ec; left; reflexivity)) as (_ & Hd).
  apply (db_blk_out ly S W mem md G (re_buf e) (re_cap e) a HAR Hin Hd).
  pose proof (db_req_ge (re_cap e)) as Hrq. clear - Ha Hj HU HU8 Hrq. lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, db_key_ptrs_len in Ha.
      assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
      destruct (HB (re_hp e, re_kh e) ltac:(unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity))
        as (_ & Hd).
      apply (db_blk_out ly S W mem md G (re_hp e) (re_kh e) a HAR Hin Hd).
      pose proof (db_req_ge (re_kh e)). unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    destruct (HB (key_addr k, Z.of_nat (length (key_text k)) + 1)
      ltac:(unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
            apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk)) as (_ & Hd).
    apply (db_blk_out ly S W mem md G _ _ a HAR Hin Hd).
    pose proof (db_req_ge (Z.of_nat (length (key_text k)) + 1)). lia.
Qed.

Lemma db_alist_fp_out : forall ly S (W : world SEGS) mem md LA l lines lo hi G,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lines -> off_img G 896 ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
(forall b, In b (alist_blks l) -> zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S W mem md LA l lines lo hi G HAR HL HGI Hlo1 Hlo2 Hhi1 Hhi2 HB r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (db_img_out G a lo hi HGI); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, db_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    assert (Ec : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
    pose proof (HB (hl_v l, AREC * hl_cap l) ltac:(unfold alist_blks; rewrite Ec; left; reflexivity)) as Hd.
    apply (db_blk_out ly S W mem md G (hl_v l) (AREC * hl_cap l) a HAR Hin Hd).
    pose proof (db_req_ge (AREC * hl_cap l)) as Hrq.
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    pose proof (HB (fst q, Z.of_nat (length (snd q)) + 1)
      ltac:(unfold alist_blks; apply in_or_app; right;
            apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hq)) as Hd.
    apply (db_blk_out ly S W mem md G _ _ a HAR Hin Hd).
    pose proof (db_req_ge (Z.of_nat (length (snd q)) + 1)). lia.
Qed.

Lemma db_asrc_fp_out : forall ly S (W : world SEGS) mem md HA h G,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h -> off_img G 896 ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(forall b, In b (asrc_blks h) -> zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S W mem md HA h G HAR HS HGI Hlo Hhi HB r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (db_img_out G a (rg_s RG) (rg_s RG + 4 * ASRC) HGI); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (HB (hs_partial h, APARTIAL) ltac:(left; reflexivity)) as Hd.
  apply (db_blk_out ly S W mem md G (hs_partial h) APARTIAL a HAR Hpb Hd).
  pose proof (db_req_ge APARTIAL). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (db_alist_fp_out ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC) G
      HAR Hpend HGI _ _ _ _ _ r Hr a Ha); unfold ASRC in *; try lia.
    intros b Hb. apply HB. right. apply in_or_app. left. exact Hb.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (db_alist_fp_out ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC) G
        HAR Hexp HGI _ _ _ _ _ r Hr a Ha); unfold ASRC in *; try lia.
      intros b Hb. apply HB. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    * refine (db_alist_fp_out ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC) G
        HAR Hheld HGI _ _ _ _ _ r Hr a Ha); unfold ASRC in *; try lia.
      intros b Hb. apply HB. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

Lemma db_aout_fp_out : forall ly S (W : world SEGS) mem md c O mx no cap out G,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
In (G, ATABLE) (ablocks B ly S) -> off_img G 896 ->
(forall b, In b (aout_blks cap out) -> zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S W mem md c O mx no cap out G HAR HOUT HTB HGI HB r Hr a Ha.
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> db_out G a).
{ intros x l Hin Hx. apply (db_G_out ly S W mem md G a HAR HTB).
  unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (db_img_out G a (rg_send_max RG) (rg_send_max RG + 8) HGI); lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; db_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; db_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; db_in | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (db_img_out G a (rg_client RG) (rg_client RG + 4) HGI); lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; db_in | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (db_img_out G a (rg_send_dead RG) (rg_send_dead RG + 1) HGI); lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; db_in | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; db_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (HB (out, cap) ltac:(unfold aout_blks; rewrite Hc0; left; reflexivity)) as Hd.
  apply (db_blk_out ly S W mem md G out cap a HAR Hin Hd).
  pose proof (db_req_ge cap). lia.
Qed.

(* W_rep.v aentry_ok_kept, for W_drain_cx.v aentry_okx *)
Lemma db_aentry_okx_kept : forall ly S W mem ly' S' W' mem' e,
aentry_okx B ly S W mem e ->
akept W mem W' mem' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' mem' e.
Proof.
intros ly S W mem ly' S' W' mem' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* s->used += n: the n bytes handed over move from the junk into the buffer *)
Lemma db_okx_used : forall ly S (W : world SEGS) m e n,
aentry_okx B ly S W m e -> 0 <= n -> n <= Z.of_nat (length (re_junk e)) -> 0 < re_cap e ->
aentry_okx B ly S W m (dr_used e n).
Proof.
intros ly S W m e n (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) Hn Hj Hc.
destruct H9 as [(Hc0 & _) | (Hcp & Hin & Hjl & Hg)]; [lia|].
unfold aentry_okx, dr_used.
cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_keys re_hp re_kh].
do 6 (split; [assumption|]).
split; [rewrite length_app, length_firstn; lia|].
split; [lia|].
split.
{ right. split; [exact Hcp|]. split; [exact Hin|]. split; [rewrite length_skipn; lia|].
  rewrite <- app_assoc, firstn_skipn. exact Hg. }
split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|]. exact H14.
Qed.

(* drain's frame without the slot 192(sp) this segment stores *)
Lemma db_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) ->
   abyte_kept W m W' m' a) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in *. cbv zeta in *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME -> (off + 8 <= 192 \/ 200 <= off) ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H3 H. apply (akept_vm W m); [intros y Hy; apply KF; change (Z.of_nat 8) with 8 in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | lia | assumption]|]).
intros i Hi. specialize (HS i Hi).
replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | lia | exact HS].
Qed.

Lemma db_nozero : forall U0, ~ In (Z_to_bv 8 0) U0 -> nozero (bzs U0).
Proof.
intros U0 H. unfold nozero, bzs. apply Forall_forall. intros b Hb.
apply in_map_iff in Hb as (x & <- & Hx). intros Ex. apply H.
replace (Z_to_bv 8 0) with x; [exact Hx|]. apply bv_eq. unfold bz in Ex. rewrite Ex. reflexivity.
Qed.

(* the line loop's registers and frame slots at its first cut *)
Lemma db_dregs : forall cx regs1 regsF (W : world SEGS) m mF,
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 27 = w64 (dxSA cx + 24) ->
getr regs1 18 = w64 (rg_s RG) -> getr regs1 9 = w64 (rg_s RG / 8) ->
getr regs1 8 = w64 ((rg_s RG + 4) / 8) -> getr regs1 21 = w64 SHADOW_OFF ->
dr_frame RG cx W m ->
val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) ->
val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) ->
val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) ->
val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) ->
getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
getr regsF 22 = getr regs1 22 -> getr regsF 27 = getr regs1 27 -> getr regsF 18 = getr regs1 18 ->
getr regsF 9 = getr regs1 9 -> getr regsF 8 = getr regs1 8 -> getr regsF 21 = getr regs1 21 ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) ->
   abyte_kept W m W mF a) ->
val_mem SEGS (arm W mF) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8) ->
dregs_line RG cx regsF W mF.
Proof.
intros cx regs1 regsF W m mF Hsp R3 R4 R22 R27 R18 R9 R8 R21 HFR M200 M56 M48 M64 E2 E3 E4 E22 E27 E18 E9 E8 E21
  KF M192.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME -> (off + 8 <= 192 \/ 200 <= off) ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W mF) (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H3 H. apply (akept_vm W m); [intros y Hy; apply KF; change (Z.of_nat 8) with 8 in Hy; lia | exact H]. }
unfold dregs_line. unfold spZ in Hsp |- *. rewrite E2, E3, E4, E22, E27, E18, E9, E8, E21.
do 9 (split; [assumption|]).
split; [exact (db_frame_kept cx W m W mF KF HFR)|].
split; [exact M192|].
unfold DRAIN_FRAME in V.
split; [apply V; [lia | lia | lia | exact M200]|].
split; [apply V; [lia | lia | lia | exact M56]|].
split; [apply V; [lia | lia | lia | exact M48]|].
apply V; [lia | lia | lia | exact M64].
Qed.

(* ---- The line loop's core at its first cut, from DDM's, in the memory the segment leaves. ---- *)
Lemma db_dlc : forall cx s1 D ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl mF mdF,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> DSAME cx e1 h1 ->
re_cap e1 = drain_b_c.ds_cap s1 -> bzs (re_U e1) = drain_b_c.ds_u s1 ->
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) ->
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 -> drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 ->
hs_eintr h1 = 0 ->
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend (dnext (dlive cx) (dxmx cx) s1) ->
hs_off h1 = drain_b_c.ds_off (dnext (dlive cx) (dxmx cx) s1) ->
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) ->
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) ->
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) ->
DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1
  (Z.of_nat (length (drl s1))) ->
RSTART cx s1 D -> dbud MT MMAX cx S1 spent tl ->
0 < dnum s1 -> bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
   ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= a < dxSA cx + 32) ->
   aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
val_mem SEGS (arm W1 mF) (dxSA cx + 24) 8 (re_used e1 + dnum s1) ->
DLC B MT MMAX RG cx s1 D 0 ly1 S1 W1 mF mdF k1 (dr_used e1 (dnum s1)) h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl mF mdF HB HM HU0 HSAME Lcap Lu Lsk LH Lka Lei
  Lpend Loff Lst Len Lecap HHIST HRS HBUD Hn Hjunk HJF KV KP M24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
fold (dsp0 cx) in Hal16, Hslo, Hshi.
pose proof HRS as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HGSB as (Hg1 & Hg2 & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (HGI : off_img (dxG cx) 896)
  by (pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR HTB) as X; rewrite RQT in X; exact X).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (_ & HG4096 & HGceil & _).
rewrite RQT in HGceil. unfold AENT, ATABLE in HSAG.
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
assert (HUL : Z.of_nat (length (drain_b_c.ds_u s1)) = re_used e1) by (rewrite <- Lu, db_bzs_len; exact HUlen).
assert (Hcp4 : 4096 + re_used e1 <= re_cap e1) by (unfold ulen in RS_gr; rewrite <- Lcap in RS_gr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [lia|].
assert (Hnle : dnum s1 <= re_cap e1 - re_used e1) by (unfold dnum, ulen; rewrite <- Lcap, HUL; lia).
assert (HNZ : nozero (drain_b_c.ds_u s1)) by (rewrite <- Lu; exact (db_nozero _ HU0)).
(* every byte the representations read: kept *)
assert (KB : forall a, db_out (dxG cx) a -> abyte_kept W1 m1 W1 mF a).
{ intros a (Ha1 & Ha2). split.
  - apply KV; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | unfold DRAIN_FRAME in *; lia | lia].
  - unfold arm. apply writable_kept. exact (KP a). }
assert (KF : forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx ->
  ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W1 mF a).
{ intros a Ha Hn2. split.
  - apply KV; [unfold DRAIN_FRAME in *; lia | unfold DRAIN_FRAME, ESTACK in *; lia | exact Hn2 | lia].
  - unfold arm. apply writable_kept. exact (KP a). }
assert (HSEP : forall b, In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap (dsv cx s1)) out1 ++
  dxrest cx) -> In b (ablocks B ly1 S1) /\ zdisjoint (dxG cx, req_size ATABLE) (fst b, req_size (snd b))).
{ intros b Hb. split; [eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hb]|].
  exact (db_sep ly1 S1 W1 m1 md1 (dxG cx) _ b HAR Hperm Hb). }
assert (HOKX1 : aentry_okx B ly1 S1 W1 mF e1).
{ apply (db_aentry_okx_kept ly1 S1 W1 m1); [exact HOKX | |].
  - intros r Hr a Ha. apply KB.
    refine (db_aentry_fp_out ly1 S1 W1 m1 md1 e1 (dxG cx) HAR HOKX _ r Hr a Ha).
    intros b Hb. apply HSEP. apply in_or_app. left. exact Hb.
  - intros b Hb. apply HSEP. apply in_or_app. left. exact Hb. }
assert (HSRC1 : asrc_at B ly1 S1 W1 mF (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1); [exact Hsrc | |].
  - intros r Hr a Ha. apply KB.
    refine (db_asrc_fp_out ly1 S1 W1 m1 md1 (dHA RG cx) h1 (dxG cx) HAR Hsrc HGI _ _ _ r Hr a Ha);
      [unfold dHA, ASRC in *; lia | unfold dHA, ASRC in *; lia |].
    intros b Hb. apply HSEP. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - intros b Hb. apply HSEP. apply in_or_app. right. apply in_or_app. left. exact Hb. }
pose proof Hout as Hout'.
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF) in Hout';
  [| intros r Hr a Ha; apply KB;
     refine (db_aout_fp_out ly1 S1 W1 m1 md1 _ _ _ _ _ _ (dxG cx) HAR Hout HTB HGI _ r Hr a Ha);
     intros b Hb; apply HSEP; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb
   | intros b Hb; apply HSEP; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
unfold DLC, LCORE. cbv zeta.
change (dskp s1 0) with (drain_b_c.ds_skip s1). change (dlH cx s1 0) with (drain_b_c.ds_H s1).
change (dlka cx s1 0) with (drain_b_c.ds_ka s1). change (dloc cx s1 0) with (drain_b_c.ds_ocap s1).
rewrite dm_dlno0. change (drlp s1 0) with (@nil (list Z)). rewrite app_nil_r.
rewrite (dm_drlq0 s1 HNZ).
change (dvirt cx s1 (drain_b_c.ds_skip s1) (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1) (drain_b_c.ds_no s1)
  (drain_b_c.ds_ocap s1)) with (dsv cx s1).
split.
{ (* the memory core *)
  unfold DMEM.
  split; [exact HJF|].
  split.
  { intros a Ha.
    assert (Hai : 65536 <= a < 6270976)
      by (destruct Ha as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
    rewrite KV; [exact (Hrom a Ha) | lia | unfold DRAIN_FRAME, ESTACK in *; lia | unfold DRAIN_FRAME in *; lia
      | unfold off_img in HGI; lia]. }
  split; [intros a Ha1 Ha2 Ha3 Hp; apply KP; exact (Hpres a Ha1 Ha2 Ha3 Hp)|].
  split; [exact Hframes|].
  split; [exact (db_frame_kept cx W1 m1 W1 mF KF HFR)|].
  split.
  { rewrite (db_entry_split (dr_used e1 (dnum s1))).
    apply (db_garr8_used W1 W1 m1 mF (dxSA cx) e1 (re_used e1 + dnum s1) Hgarr Hpad1 Hpad2); [|lia | exact M24].
    intros x Hx Hn2. apply KV; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | unfold DRAIN_FRAME in *; lia | exact Hn2]. }
  split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 mF); [exact (KP (dxSA cx + i)) | exact (Hawr i Hi)]|].
  split; [apply db_okx_used; [exact HOKX1 | lia | lia | lia]|].
  split; [exact HSRC1|].
  split.
  { intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o.
    split; [|split; [|exact Ho]]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx; apply KB;
    apply (db_img_out (dxG cx) x (rg_s RG) (rg_s RG + 4 * ASRC) HGI); unfold ASRC in *;
    change (Z.of_nat 4) with 4 in Hx; clear - Hx Hi Hg1 Hg2; lia. }
  split.
  { intros x Hx Hn2. destruct (Hgsk x Hx Hn2) as [A1 A2].
    assert (Hxl : db_out (dxG cx) x)
      by (apply (db_img_out (dxG cx) x (rg_s RG) (rg_s RG + 4 * ASRC) HGI); unfold ASRC in *; lia).
    destruct (KB x Hxl) as [B1 B2]. split; [rewrite B1; exact A1 | intros Hw; apply B2; apply A2; exact Hw]. }
  split; [exact Hout'|].
  split; [exact Hlivout | exact Hperm]. }
split.
{ (* the round state the line loop sees *)
  unfold DLINK, dr_used. cbn [re_cap re_U re_skip re_keys re_hp re_kh].
  split; [exact Lcap|].
  split; [rewrite db_bzs_app, Lu, Hjunk; reflexivity|].
  split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|]. split; [exact Lei|].
  split; [exact Lpend|]. split; [exact Loff|]. split; [exact Lst|]. split; [exact Len|]. split; [exact Lecap|].
  exact (dm_dwf_virt RG HGSB cx s1 RS_wf RS_st Hn). }
split; [exact HSAME|].
split; [exact HHIST|].
split; [exact HRS | exact HBUD].
Qed.

(* ---- The symbolic state at DDM, from the cut's concrete facts. ---- *)
Lemma db_entry : forall (W : world SEGS) regs1 m1 sp SA BUF USED n,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 27 = w64 (SA + 24) -> getr regs1 26 = w64 (SA + 16) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 19 = w64 n -> 1 <= n <= 16384 ->
4096 <= SA -> SA + 56 <= DB_HI -> SA + 56 <= sp ->
0 <= BUF < 2 ^ 64 -> 0 <= USED < 2 ^ 64 ->
val_mem SEGS (arm W m1) (sp + 208) 8 (SA + 8) ->
val_mem SEGS (arm W m1) (sp + 216) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W m1) (sp + 224) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W m1) (SA + 16) 8 BUF ->
val_mem SEGS (arm W m1) (SA + 24) 8 USED ->
(forall o, 192 <= o < 200 -> writable_at SEGS (arm W m1) (sp + o)) ->
awr W m1 SA AENT ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (db_extra SA BUF USED))) ss_db
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_join)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 sp SA BUF USED n Hsp Hlo Hhi Hal R27 R26 R21 R19 Hn HSA1 HSA2 HSA3 HBUF HUSED M208 M216 M224
  MBUF MUSED HW Hawr.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (db_extra SA BUF USED))).
assert (E2 : ew E 2 = getr regs1 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E19 : ew E 19 = getr regs1 19)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 19 19%bv eq_refl)).
assert (E21 : ew E 21 = getr regs1 21)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 21 21%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 BUF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 USED)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E21' : ew E 21 = Z_to_bv 64 SB) by (rewrite E21, R21; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (Usa : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; unfold DB_HI in *; lia).
pose proof (db_shadow_range (SA + 16) ltac:(unfold DB_HI in *; lia)) as SR16.
pose proof (db_shadow_range (SA + 24) ltac:(unfold DB_HI in *; lia)) as SR24.
unfold DB_HI in HSA2. unfold DRAIN_FRAME in Hhi.
unfold ss_db. apply pa_entry_st_ok_full.
- unfold db_regs. apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
    | intros X; discriminate X |].
  + rewrite (den_atom E 32%nat SA 24 E32) by lia. exact R27.
  + rewrite (den_atom E 32%nat SA 16 E32) by lia. exact R26.
- vm_compute. reflexivity.
- unfold db_regions, db_frame, db_ent.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?Usa.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 208 8 (SOff 32 8) (SA + 8));
      [rewrite (den_atom E 32%nat SA 8 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M208].
    * apply (chunk_ok_val SEGS E _ sp 216 8 _ (shadow_addr (SA + 16)));
      [apply db_den; rewrite (db_U_shadow E 32 SA 16 E32 E21') by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact SR16 | cbn; lia | exact M216].
    * apply (chunk_ok_val SEGS E _ sp 224 8 _ (shadow_addr (SA + 24)));
      [apply db_den; rewrite (db_U_shadow E 32 SA 24 E32 E21') by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact SR24 | cbn; lia | exact M224].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Hawr o ltac:(unfold AENT; lia))|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ SA 16 8 (SOff 33 0) BUF);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact MBUF].
    * apply (chunk_ok_val SEGS E _ SA 24 8 (SOff 34 0) USED);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact MUSED].
- apply pairwise_disjoint_of_extents. unfold db_regions, db_frame, db_ent, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usa.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [db_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usa, E21', E19, R19. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, DB_HI. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* ---- DROPB: DDM 0x83668 -> s->used += n (0x83684) -> memchr #1 (0x836a4) -> DLL (a NUL at q) / DLR (none). ---- *)
Ltac db_awr_frame UspX :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
eapply awr_ok_cons_stack_off; [reflexivity | exact UspX | cbn; lia | cbn; lia | apply awr_ok_nil].

Theorem dr_dropb : dr_dropb_stmt B MT MMAX RG.
Proof.
unfold dr_dropb_stmt. intros cx s1 D W1 c1 HB HDDM Hdll Hdlr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
unfold DDM in HDDM.
destruct HDDM as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hcfg & Hsp & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R22 & R25 & R26 & R27 &
  HFR & M56 & M64 & M48 & M200 & Hn0 & Hn16 & Hjunk & HMEM & HU0 & HUa & HSAME &
  Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & HHIST & HRS & Hfut & HBUD).
pose proof HFR as HFR'. unfold dr_frame in HFR'. cbv zeta in HFR'.
destruct HFR' as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & HBx10 & HGin0 & HGSA & HSAG & HBrest).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (_ & HG4096 & HGceil & HGia & _).
rewrite RQT in HGceil, HGia. unfold AENT, ATABLE in HSAG.
assert (HGI : off_img (dxG cx) 896)
  by (pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR HTB) as X; rewrite RQT in X; exact X).
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld & HND1 & HND2
  & Hkeys).
pose proof HRS as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
assert (HUL : Z.of_nat (length (drain_b_c.ds_u s1)) = re_used e1) by (rewrite <- Lu, db_bzs_len; exact HUlen).
assert (Hcp4 : 4096 + re_used e1 <= re_cap e1) by (unfold ulen in RS_gr; rewrite <- Lcap in RS_gr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (_ & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil.
assert (Hnle : dnum s1 <= re_cap e1 - re_used e1) by (unfold dnum, ulen; rewrite <- Lcap, HUL; lia).
assert (HNZ : nozero (drain_b_c.ds_u s1)) by (rewrite <- Lu; exact (db_nozero _ HU0)).
assert (HdW : bzs (re_U e1 ++ firstn (Z.to_nat (dnum s1)) (re_junk e1)) = dW s1)
  by (unfold dW; rewrite db_bzs_app, Lu, Hjunk; reflexivity).
assert (HLW : Z.of_nat (length (dW s1)) = re_used e1 + dnum s1)
  by (rewrite <- HdW, db_bzs_len, length_app, length_firstn; lia).
assert (HWB : bzs (re_U e1 ++ re_junk e1) = dW s1 ++ bzs (skipn (Z.to_nat (dnum s1)) (re_junk e1))).
{ rewrite <- (firstn_skipn (Z.to_nat (dnum s1)) (re_junk e1)) at 1. rewrite app_assoc, db_bzs_app, HdW. reflexivity. }
assert (HSEPbuf : zdisjoint (dxG cx, req_size ATABLE) (fst (re_buf e1, re_cap e1), req_size (snd (re_buf e1, re_cap e1)))).
{ apply (db_sep ly1 S1 W1 m1 md1 (dxG cx) _ (re_buf e1, re_cap e1) HAR Hperm).
  apply in_or_app. left. unfold aentry_blks. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by lia. left. reflexivity. }
unfold zdisjoint in HSEPbuf. cbn [fst snd] in HSEPbuf. rewrite RQT, RQC in HSEPbuf.
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
clear memS HJi.
pose proof (db_entry_buf W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MBUF.
pose proof (db_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MUSED.
set (n := dnum s1) in *.
(* ---- the symbolic state at DDM ---- *)
pose proof (db_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_used e1) n Hsp
  ltac:(unfold DRAIN_FRAME; lia) ltac:(unfold DRAIN_FRAME; lia)
  ltac:(unfold DRAIN_FRAME; rewrite Zminus_mod, Hal16; reflexivity)
  R27 R26 R21 R19 ltac:(lia) ltac:(lia) ltac:(unfold DB_HI; lia) ltac:(unfold DRAIN_FRAME; lia)
  ltac:(lia) ltac:(lia) F208 F216 F224 MBUF MUSED
  ltac:(intros o' Ho'; apply (apresent_writable SEGS); apply HJpres; unfold DRAIN_FRAME in *; lia) Hawr) as HS.
remember (Eimg (Ereg regs1 (db_extra (dxSA cx) (re_buf e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs1 r).
{ intros n0 r Hn' Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (Usa : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS dbBx DB_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E dbBx 32 (dxSA cx + 16) 16 (dxSA cx) 16 32).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE);
      [exact HAR | exact HTB | lia | rewrite RQT; lia].
  - unfold dbBx. rewrite (U_atom E 21 SB E21) by (unfold SB; lia). reflexivity.
  - apply (U_atom E 32 (dxSA cx) E32). lia.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    rewrite Z.min_l, Z.max_r in Hx by lia. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_join)) with (Z_to_bv 64 (BASE + A_dr_join)).
(* ---- 0x83668 .. 0x836a4: n < 0 / n == 0 refuted, the two shadow checks fold, s->used += n, the call's arguments ---- *)
paj_run_tok RUN HS HJ SHOK db_Bspan.
{ cbn [ss_mem ss_db db_regions].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  - intros x Hx. cbn [db_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp in Hx.
    left. split; [left; unfold DRAIN_FRAME in *; lia | lia].
  - intros x Hx. cbn [db_ent YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usa in Hx.
    left. split; [|lia]. right. left. split.
    + unfold dFP, dr_fp. apply inFP_cons. left. unfold AENT. lia.
    + exists (dxG cx), ATABLE. split; [exact HTB | rewrite RQT; lia]. }
rename ms into msA.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem msA)) |- _ => rename Hg into GRA end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. db_rreg HS (12%bv : bv 5) Q12.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
(* what the run kept: everything but its two write windows *)
assert (KEEP1 : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) ->
  ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W1) (ms_mem msA) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy N1 N2. apply (aview_kept_out E (ss_mem ss_db) (w_H W1) m1 (ms_mem msA) HFr y Hy).
  intros (r & Hin & Hr). cbn [ss_mem ss_db db_regions In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [db_frame db_ent YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?Usp, ?Usa in Hr; lia. }
(* s->used now holds used + n *)
assert (M24 : val_mem SEGS (arm W1 (ms_mem msA)) (dxSA cx + 24) 8 (re_used e1 + n)).
{ replace (re_used e1 + n) with (n + re_used e1) by lia.
  apply (field_of_region E _ 32 (dxSA cx) _ 16 32 24 32 24 8 (SAlu ALU_ADD (SOff 19 0) (SOff 34 0)) _ HR1 Usa).
  - cbn. db_in.
  - apply db_den. apply (db_U_add E 19 34 n (re_used e1) E19 E34); lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (Usp1 : spZ (ms_regs msA) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (G10 : getr (ms_regs msA) 10 = w64 (re_buf e1)) by (rewrite Q10; exact E33).
set (nn := re_used e1 + n).
assert (G12 : getr (ms_regs msA) 12 = w64 nn).
{ rewrite Q12. apply db_den. unfold nn. rewrite Z.add_comm. apply (db_U_add E 19 34 n (re_used e1) E19 E34); lia. }
(* the buffer's bytes, as memchr reads them *)
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) (ms_mem msA) (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite KEEP1 by (unfold DRAIN_FRAME in *; lia).
  rewrite (db_garr8_aview W1 m1 (re_buf e1) _ j Hbuf8) by (rewrite db_bzs_len, length_app; lia).
  rewrite HWB, app_nth1 by lia. reflexivity. }
assert (ROM1 : rom_view SEGS W1 (ms_mem msA)).
{ intros x Hx.
  assert (Hai : 65536 <= x < 6270976)
    by (destruct Hx as (sg & Hsg & _ & Hr); exact (pa_img_range x ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite KEEP1; [exact (Hrom x Hx) | lia | unfold DRAIN_FRAME in *; lia | unfold off_img in HGI; lia]. }
assert (SRC : src_ok SEGS W1 (ms_regs msA) (ms_mem msA) (re_buf e1) nn).
{ intros y Hy. split.
  - replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
    rewrite BV by (unfold nn in Hy; lia). discriminate.
  - rewrite Usp1. unfold DRAIN_FRAME, ESTACK in *. lia. }
assert (AMR : amem_range (re_buf e1) nn).
{ unfold nn. unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. rewrite RQC in HBia.
  lia. }
pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARA.
assert (RA : range_addressable (aview SEGS (w_H W1) (ms_mem msA)) SHADOW_OFF (re_buf e1) nn)
  by (apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ (re_buf e1) (re_cap e1) _ _ HARA Hbin);
      [lia | rewrite RQC; unfold nn; lia]).
assert (HV : 0 < nn -> shadow_hull_vis (aview SEGS (w_H W1) (ms_mem msA)) (re_buf e1) nn)
  by (intros Hnn; apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ (re_buf e1) (re_cap e1) _ _ HARA Hbin);
      [lia | rewrite RQC; unfold nn; lia | exact Hnn]).
pose proof (consts_view_of_rom_view SEGS 0x10350 0x10370 W1 (ms_mem msA) HCROM ROM1) as CV.
(* ---- memchr (s->buf, 0, s->used) ---- *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_memchr)
    (fun _ => False)
    (fun regs' (_ : word -> option byte) => exists k, first_byte SEGS W1 (ms_mem msA) (re_buf e1) nn 0 k /\
       getr regs' 10 = (if k <? nn then w64 (re_buf e1 + k) else w64 0))
    W1 (ms_regs msA) (ms_mem msA) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5052)) HG eq_refl HJ).
  - rewrite Usp1. lia.
  - rewrite HDF. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros _. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE _. eapply SRr_mono.
    { exact (AMEMCHR ly1 S1 W1 (ms_regs msA) (ms_mem msA) _ (re_buf e1) 0 nn HPRE G10 Q11 G12
        ltac:(lia) ltac:(unfold nn; lia) ltac:(lia) ltac:(unfold nn; lia) SRC AMR RA HV CV). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Hres) & Hfr2 & Hpres2).
(* ---- after the call: the frame region kept, the caller-saved registers havocked from atom 35 ---- *)
assert (KR : region_kept SEGS E (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) mem2) db_frame).
{ apply (region_kept_aview E (w_H W1) (ms_mem msA) mem2 2 (dsp0 cx - DRAIN_FRAME) 192 232 192 200 _ Usp).
  - intros y Hy. apply Hfr2; [lia | intros Hf; exact Hf | unfold DRAIN_FRAME, ESTACK in *; lia].
  - exact Hpres2. }
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
specialize (HS2 ltac:(constructor; [exact KR | constructor])).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (SHOK2 : sh_ok SEGS dbBx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
assert (Usp2 : bv_unsigned (ew Ea 2) = dsp0 cx + - DRAIN_FRAME) by (rewrite (OLDa 2%nat ltac:(lia)), Usp; lia).
(* ---- 0x836a8 .. 0x836b8: s7 = the result, 192(sp) = (SA + 8) >> 3, the beqz ---- *)
paj_run_tok RUN HS HJ2 SHOK2 db_Bspan. { apply awr_ok_x_of0. db_awr_frame Usp2. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFrB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hg into GRB end.
assert (KEEPB : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W1) (ms_mem msB) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy N1 N2 N3.
  rewrite (aview_kept_out Ea _ (w_H W1) mem2 (ms_mem msB) HFrB y Hy).
  - rewrite (Hfr2 y Hy (fun Hf => Hf) ltac:(unfold DRAIN_FRAME, ESTACK in *; lia)). exact (KEEP1 y Hy N2 N3).
  - intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia. }
assert (PRESB : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msB) y).
{ intros y Hp. apply (apresent_grows _ _ _ _ GRB). apply Hpres2. exact (apresent_grows _ _ _ _ GRA Hp). }
assert (M24B : val_mem SEGS (arm W1 (ms_mem msB)) (dxSA cx + 24) 8 (re_used e1 + n)).
{ apply (akept_vm W1 (ms_mem msA)); [|exact M24]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. split.
  - rewrite (aview_kept_out Ea _ (w_H W1) mem2 (ms_mem msB) HFrB x ltac:(lia)).
    + apply Hfr2; [lia | intros Hf; exact Hf | unfold DRAIN_FRAME, ESTACK in *; lia].
    + intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia.
  - intros Hw. unfold arm. apply (writable_kept (w_H W1) (ms_mem msA) (ms_mem msB)); [|exact Hw]. intros Hp.
    apply (apresent_grows _ _ _ _ GRB). apply Hpres2. exact Hp. }
set (a0v := if kk <? nn then re_buf e1 + kk else 0).
assert (HA0 : ew Ea 39 = Z_to_bv 64 a0v) by (rewrite <- R10b, Hres; unfold a0v; destruct (kk <? nn); reflexivity).
destruct Hfb as (Hk0 & Hkb & Hkz).
assert (Ra0 : 0 <= a0v < 2 ^ 64) by (unfold a0v, nn in *; destruct (kk <? re_used e1 + n); lia).
psrr_branch_tok RUN BR HS SHOK2 db_Bspan.
- (* s7 = 0: no NUL in the buffer; 0x83a48 mv s10, s8; DLR with p = 0 *)
  rewrite branch_eq_U, (U_atom Ea 39 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk = nn).
  { destruct (Z_lt_ge_dec kk nn) as [Hl | Hl]; [|lia]. exfalso. unfold a0v in Hc.
    rewrite (proj2 (Z.ltb_lt kk nn) Hl) in Hc. apply Z.eqb_eq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ2 SHOK2 db_Bspan A_dr_rest. { apply awr_ok_x_of0. db_awr_frame Usp2. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hg into GRF end.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRF. cbn [ms_mem restrict] in HRF.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (24%bv : bv 5) P24. db_rreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy N1 N2 N3. rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF y Hy).
    - exact (KEEPB y Hy N1 N2 N3).
    - intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia. }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ _ GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hn2. split; [apply KEEPF; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | exact Hn2 | lia]|].
    unfold arm. apply (writable_kept (w_H W1) m1 (ms_mem msF)). exact (PRESF y). }
  assert (M24F : val_mem SEGS (arm W1 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + n)).
  { apply (akept_vm W1 (ms_mem msB)); [|exact M24B]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. split.
    - rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF x ltac:(lia)); [reflexivity|].
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia.
    - intros Hw. unfold arm. apply (writable_kept (w_H W1) (ms_mem msB) (ms_mem msF)); [|exact Hw]. intros Hp.
      exact (apresent_grows _ _ _ _ GRF Hp). }
  assert (M192F : val_mem SEGS (arm W1 (ms_mem msF)) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8)).
  { apply (slot_of_region Ea _ _ _ _ _ _ _ 192 (SAlu ALU_SRL (SOff 32 8) (SLit 3)) _ HRF).
    - rewrite Usp2. lia.
    - cbn. db_in.
    - apply db_den. apply (db_U_srl Ea 32 (dxSA cx) 8); [rewrite (OLDa 32%nat ltac:(lia)); exact E32 | lia | lia].
    - pose proof (db_div8 (dxSA cx + 8) ltac:(lia)). lia. }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdlr W1). unfold DLR.
  exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, (dr_used e1 n), h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (db_dregs cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hsp R3 R4 R22 R27 R18 R9 R8 R21 HFR M200 M56 M48 M64);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity]
      | apply (RK _ 9%nat P9); [lia | reflexivity] | apply (RK _ 8%nat P8); [lia | reflexivity]
      | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF | exact M192F ].
    rewrite P27, (OLDa 32%nat ltac:(lia)), E32, R27. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  split; [rewrite P24, (OLDa 33%nat ltac:(lia)), E33; unfold w64; f_equal; cbn [re_buf dr_used]; lia|].
  split.
  { rewrite P25. apply db_den. rewrite Nat.sub_0_r, HLW, Z.add_comm.
    apply (db_U_add Ea 19 34 n (re_used e1));
      [rewrite (OLDa 19%nat ltac:(lia)); exact E19 | rewrite (OLDa 34%nat ltac:(lia)); exact E34 | lia | lia | lia]. }
  split; [rewrite P26, (OLDa 33%nat ltac:(lia)), E33; reflexivity|].
  split; [apply (dm_dbound0 RG)|].
  split.
  { intros i Hi. destruct (Nat.lt_ge_cases i (length (dW s1))) as [Hil | Hil].
    - destruct (Hkb (Z.of_nat i) ltac:(lia)) as (bb & Hb & Hb0).
      rewrite BV in Hb by exact Hil. injection Hb as <-.
      rewrite (nth_error_nth' (dW s1) 0) by exact Hil.
      intros Hn0'. injection Hn0' as Hn0'. exact (Hb0 Hn0').
    - rewrite (proj2 (nth_error_None (dW s1) i) Hil). discriminate. }
  split.
  { exact (db_dlc cx s1 D ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF HB HMEM HU0 HSAME
      Lcap Lu Lsk LH Lka Lei Lpend Loff Lst Len Lecap HHIST HRS HBUD Hn0 Hjunk HJ2 KEEPF PRESF M24F). }
  rewrite dm_dlno0, (dm_drlq0 s1 HNZ). exact Hfut.
- (* s7 <> 0: the first NUL at s->buf + kk; DLL with p = 0, q = kk *)
  rewrite branch_eq_U, (U_atom Ea 39 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk < nn).
  { destruct (Z_lt_ge_dec kk nn) as [Hl | Hl]; [exact Hl|]. exfalso. unfold a0v in Hc.
    rewrite (proj2 (Z.ltb_ge kk nn) ltac:(lia)) in Hc. cbn in Hc. discriminate Hc. }
  assert (Ha0 : a0v = re_buf e1 + kk) by (unfold a0v; rewrite (proj2 (Z.ltb_lt kk nn) Hkk); reflexivity).
  paj_run_to_tok RUNTO HS HJ2 SHOK2 db_Bspan A_dr_line. { apply awr_ok_x_of0. db_awr_frame Usp2. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hg into GRF end.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRF. cbn [ms_mem restrict] in HRF.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy N1 N2 N3. rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF y Hy).
    - exact (KEEPB y Hy N1 N2 N3).
    - intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia. }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ _ GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hn2. split; [apply KEEPF; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | exact Hn2 | lia]|].
    unfold arm. apply (writable_kept (w_H W1) m1 (ms_mem msF)). exact (PRESF y). }
  assert (M24F : val_mem SEGS (arm W1 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + n)).
  { apply (akept_vm W1 (ms_mem msB)); [|exact M24B]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. split.
    - rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF x ltac:(lia)); [reflexivity|].
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia.
    - intros Hw. unfold arm. apply (writable_kept (w_H W1) (ms_mem msB) (ms_mem msF)); [|exact Hw]. intros Hp.
      exact (apresent_grows _ _ _ _ GRF Hp). }
  assert (M192F : val_mem SEGS (arm W1 (ms_mem msF)) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8)).
  { apply (slot_of_region Ea _ _ _ _ _ _ _ 192 (SAlu ALU_SRL (SOff 32 8) (SLit 3)) _ HRF).
    - rewrite Usp2. lia.
    - cbn. db_in.
    - apply db_den. apply (db_U_srl Ea 32 (dxSA cx) 8); [rewrite (OLDa 32%nat ltac:(lia)); exact E32 | lia | lia].
    - pose proof (db_div8 (dxSA cx + 8) ltac:(lia)). lia. }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdll (Z.to_nat kk) W1). unfold DLL.
  exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, (dr_used e1 n), h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (db_dregs cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hsp R3 R4 R22 R27 R18 R9 R8 R21 HFR M200 M56 M48 M64);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity]
      | apply (RK _ 9%nat P9); [lia | reflexivity] | apply (RK _ 8%nat P8); [lia | reflexivity]
      | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF | exact M192F ].
    rewrite P27, (OLDa 32%nat ltac:(lia)), E32, R27. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  split; [rewrite P23, HA0, Ha0; unfold w64; f_equal; cbn [re_buf dr_used]; lia|].
  split; [rewrite P24, (OLDa 33%nat ltac:(lia)), E33; unfold w64; f_equal; cbn [re_buf dr_used]; lia|].
  split; [apply (dm_dbound0 RG)|].
  split; [lia|].
  split.
  { pose proof (Hkz Hkk) as Hz.
    replace (re_buf e1 + kk) with (re_buf e1 + Z.of_nat (Z.to_nat kk)) in Hz by lia.
    rewrite BV in Hz by lia. injection Hz as Hz.
    rewrite (nth_error_nth' (dW s1) 0) by lia. rewrite Hz. reflexivity. }
  split.
  { intros i Hi. destruct (Hkb (Z.of_nat i) ltac:(lia)) as (bb & Hb & Hb0).
    rewrite BV in Hb by lia. injection Hb as <-.
    rewrite (nth_error_nth' (dW s1) 0) by lia.
    intros Hn0'. injection Hn0' as Hn0'. exact (Hb0 Hn0'). }
  split.
  { exact (db_dlc cx s1 D ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF HB HMEM HU0 HSAME
      Lcap Lu Lsk LH Lka Lei Lpend Loff Lst Len Lecap HHIST HRS HBUD Hn0 Hjunk HJ2 KEEPF PRESF M24F). }
  rewrite dm_dlno0, (dm_drlq0 s1 HNZ). exact Hfut.
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice B, 2026-10-30): dr_dropb_x proves W_drain_dropb_cx.v's
   dr_dropb_stmt_x, the walk dr_dropb above over W_drain_cx_x.v's Section variables (B PST ARx MT RP MMAX RG): the
   same run (the n < 0 / n == 0 arms refuted, s->used += n at 0x83684, memchr #1 at 0x836a4 through AMEMCHR, W_sites_x.v
   amemchr_realizesM_x entered by aj_gx_entry_at_x, then the beqz to DLL_x / DLR_x at p = 0), the entry's ghost list Hp
   and budget kr carried, the cut's own ghost list Hp1 kept (a runtime entry keeps it), and DDM_x's dbud_x carried to
   the line loop's cut unchanged (no allocator call: state, blocks and trace are kept).  The lemmas that read AR have
   twins NAME_x over ARx.  Where the AR text reads the table block's apartness from the image through blk_off_imgP
   (whose ARx form needs an image-cover hypothesis), the twins read it from the client-image law alx_client_img for
   image bytes (db_img_out_x; the image bytes are G_DR's by HG and aout_at's three read-only cells by HGO), and
   db_sep_x cites W_drain_cx_x.v's sep_blocks_perm_x (YCbq.v's sep_blocks_perm over ARx), as db_sep cites
   sep_blocks_perm.  The AR-free lemmas are cited; the AR file's Section-local Ltacs are restated with _x.
   Everything above this line is unchanged; the twin only adds names (the AR name with _x).
   ============================================================================================================ *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x.
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
(* the generic-relation fact the walk reads (a Theorem Labs lane's text, 2026-10-30) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* W_drain_cx_x.v Section c's hypotheses the walk reads (its text) *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* ALLOC_TAIL is no hypothesis: W_drain_cx_x.alloc_tail_x SEGS B ARx LAWS *)

(* ---- The AR file's Section-local Ltacs (gone at its End c / End b), restated. ---- *)
Ltac db_in_x := repeat (first [left; reflexivity | right]).

Ltac db_rreg_x HS r Hr :=
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

Ltac db_awr_frame_x UspX :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
eapply awr_ok_cons_stack_off; [reflexivity | exact UspX | cbn; lia | cbn; lia | apply awr_ok_nil].

(* ---- Where the cut's representations live (db_out, above), over ARx. ---- *)
(* db_blk_out over the blocks law alx_blocks *)
Lemma db_blk_out_x : forall ly S Hp (W : world SEGS) mem md G q n a,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> zdisjoint (G, req_size ATABLE) (q, req_size n) ->
q <= a < q + req_size n -> db_out G a.
Proof.
intros ly S Hp W mem md G q n a HAR Hin Hd Ha.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQ in Hd. unfold db_out. lia.
Qed.

(* an image byte is below the ceiling and off the relay table's block (the client-image law alx_client_img): the
   ARx form of db_img_out, from the byte's image membership in place of the block's off_img *)
Lemma db_img_out_x : forall ly S Hp (W : world SEGS) mem md G a,
ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> YG0d.in_img SEGS a -> db_out G a.
Proof.
intros ly S Hp W mem md G a HAR HTB Himg.
pose proof (pa_segs_low a Himg) as Hl. pose proof (pa_img_range a Himg) as Hr.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
unfold db_out. split; [lia|].
destruct (Z_lt_ge_dec a G) as [H1|H1]; [left; exact H1|].
destruct (Z_lt_ge_dec a (G + 896)) as [H2|H2]; [|right; lia].
assert (Hin2 : G <= a < G + req_size ATABLE) by (rewrite RQ; lia).
exfalso. apply (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md a HAR
  (or_introl (ex_intro _ G (ex_intro _ ATABLE (conj HTB Hin2)))))).
exact Himg.
Qed.

(* db_G_out: a byte of G_DR is an image byte (HG) *)
Lemma db_G_out_x : forall ly S Hp (W : world SEGS) mem md G a,
ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> inG (G_DR B RG) a -> db_out G a.
Proof.
intros ly S Hp W mem md G a HAR HTB Ha.
exact (db_img_out_x ly S Hp W mem md G a HAR HTB (proj1 (HG a Ha))).
Qed.

(* db_sep: the relay table's block is apart from every other block the cut names (W_drain_cx_x.v sep_blocks_perm_x) *)
Lemma db_sep_x : forall ly S Hp (W : world SEGS) mem md G rest b,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((G, ATABLE) :: rest) -> In b rest ->
zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b)).
Proof.
intros ly S Hp W mem md G rest b HAR HP Hb.
apply in_split in Hb as (r1 & r2 & ->).
change (zdisjoint (block_rng (G, ATABLE)) (block_rng b)).
apply (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W mem md (G, ATABLE) b (r1 ++ r2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

Lemma db_aentry_fp_out_x : forall ly S Hp (W : world SEGS) mem md e G,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly S) /\ zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S Hp W mem md e G HAR HE HB r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & HU8 & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct (HB (re_buf e, re_cap e) ltac:(unfold aentry_blks; rewrite Ec; left; reflexivity)) as (_ & Hd).
  apply (db_blk_out_x ly S Hp W mem md G (re_buf e) (re_cap e) a HAR Hin Hd).
  pose proof (db_req_ge RG (re_cap e)) as Hrq. clear - Ha Hj HU HU8 Hrq. lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, (db_key_ptrs_len RG) in Ha.
      assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
      destruct (HB (re_hp e, re_kh e) ltac:(unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity))
        as (_ & Hd).
      apply (db_blk_out_x ly S Hp W mem md G (re_hp e) (re_kh e) a HAR Hin Hd).
      pose proof (db_req_ge RG (re_kh e)). unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    destruct (HB (key_addr k, Z.of_nat (length (key_text k)) + 1)
      ltac:(unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
            apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk)) as (_ & Hd).
    apply (db_blk_out_x ly S Hp W mem md G _ _ a HAR Hin Hd).
    pose proof (db_req_ge RG (Z.of_nat (length (key_text k)) + 1)). lia.
Qed.

(* db_alist_fp_out: the list head's cell from its image membership (the range [lo, hi) of image bytes) *)
Lemma db_alist_fp_out_x : forall ly S Hp (W : world SEGS) mem md LA l lines lo hi G,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> In (G, ATABLE) (ablocks B ly S) ->
(forall x, lo <= x < hi -> YG0d.in_img SEGS x) -> lo <= LA -> LA + 16 <= hi ->
(forall b, In b (alist_blks l) -> zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S Hp W mem md LA l lines lo hi G HAR HL HTB HIMG Hlo2 Hhi1 HB r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (db_img_out_x ly S Hp W mem md G a HAR HTB). apply HIMG. lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, (db_recs_len RG) in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    assert (Ec : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
    pose proof (HB (hl_v l, AREC * hl_cap l) ltac:(unfold alist_blks; rewrite Ec; left; reflexivity)) as Hd.
    apply (db_blk_out_x ly S Hp W mem md G (hl_v l) (AREC * hl_cap l) a HAR Hin Hd).
    pose proof (db_req_ge RG (AREC * hl_cap l)) as Hrq.
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    pose proof (HB (fst q, Z.of_nat (length (snd q)) + 1)
      ltac:(unfold alist_blks; apply in_or_app; right;
            apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hq)) as Hd.
    apply (db_blk_out_x ly S Hp W mem md G _ _ a HAR Hin Hd).
    pose proof (db_req_ge RG (Z.of_nat (length (snd q)) + 1)). lia.
Qed.

(* db_asrc_fp_out: the source slot and its list heads are g_s bytes, image bytes by HG *)
Lemma db_asrc_fp_out_x : forall ly S Hp (W : world SEGS) mem md HA h G,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h -> In (G, ATABLE) (ablocks B ly S) ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(forall b, In b (asrc_blks h) -> zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S Hp W mem md HA h G HAR HS HTB Hlo Hhi HB r Hr a Ha.
assert (HIMG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> YG0d.in_img SEGS x).
{ intros x Hx. refine (proj1 (HG x _)). unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (db_img_out_x ly S Hp W mem md G a HAR HTB). apply HIMG. unfold ASRC in *. lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (HB (hs_partial h, APARTIAL) ltac:(left; reflexivity)) as Hd.
  apply (db_blk_out_x ly S Hp W mem md G (hs_partial h) APARTIAL a HAR Hpb Hd).
  pose proof (db_req_ge RG APARTIAL). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (db_alist_fp_out_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC) G
      HAR Hpend HTB HIMG _ _ _ r Hr a Ha); unfold ASRC in *; try lia.
    intros b Hb. apply HB. right. apply in_or_app. left. exact Hb.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (db_alist_fp_out_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC) G
        HAR Hexp HTB HIMG _ _ _ r Hr a Ha); unfold ASRC in *; try lia.
      intros b Hb. apply HB. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    * refine (db_alist_fp_out_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC) G
        HAR Hheld HTB HIMG _ _ _ r Hr a Ha); unfold ASRC in *; try lia.
      intros b Hb. apply HB. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

(* db_aout_fp_out: aout_at's cells are G_DR's (HG) or the three read-only cells of HGO, all image bytes *)
Lemma db_aout_fp_out_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out G,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
In (G, ATABLE) (ablocks B ly S) ->
(forall b, In b (aout_blks cap out) -> zdisjoint (G, req_size ATABLE) (fst b, req_size (snd b))) ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> db_out G a.
Proof.
intros ly S Hp W mem md c O mx no cap out G HAR HOUT HTB HB r Hr a Ha.
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> db_out G a).
{ intros x l Hin Hx. apply (db_G_out_x ly S Hp W mem md G a HAR HTB).
  unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (GO : forall x l, In (x, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] ->
  x <= a < x + l -> db_out G a).
{ intros x l Hin Hx. apply (db_img_out_x ly S Hp W mem md G a HAR HTB). refine (proj1 (HGO a _)).
  unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- apply (GO (rg_send_max RG) 8); [db_in_x | lia].
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; db_in_x | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; db_in_x | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; db_in_x | lia].
- apply (GO (rg_client RG) 4); [db_in_x | lia].
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; db_in_x | lia].
- apply (GO (rg_send_dead RG) 1); [db_in_x | lia].
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; db_in_x | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; db_in_x | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (HB (out, cap) ltac:(unfold aout_blks; rewrite Hc0; left; reflexivity)) as Hd.
  apply (db_blk_out_x ly S Hp W mem md G out cap a HAR Hin Hd).
  pose proof (db_req_ge RG cap). lia.
Qed.


(* The pieces of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cf rules and every carrier or statement it names
   -> their R twins; every other token is the strict text's. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* ---- db_dlc: the line loop's core at its first cut, from DDM_x's, in the memory the segment leaves. ---- *)
Lemma db_dlc_xR : forall cx Hp kr s1 D ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl mF mdF,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> DSAME cx e1 h1 ->
re_cap e1 = drain_b_c.ds_cap s1 -> bzs (re_U e1) = drain_b_c.ds_u s1 ->
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) ->
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 -> drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 ->
hs_eintr h1 = 0 ->
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend (dnext (dlive cx) (dxmx cx) s1) ->
hs_off h1 = drain_b_c.ds_off (dnext (dlive cx) (dxmx cx) s1) ->
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) ->
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) ->
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) ->
DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1
  (Z.of_nat (length (drl s1))) ->
RSTART cx s1 D -> dbud_x B MT RP MMAX cx kr ly1 S1 spent tl ->
0 < dnum s1 -> bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
   ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= a < dxSA cx + 32) ->
   aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
val_mem SEGS (arm W1 mF) (dxSA cx + 24) 8 (re_used e1 + dnum s1) ->
DLC_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D 0 ly1 S1 Hp1 W1 mF mdF k1 (dr_used e1 (dnum s1)) h1 out1 ev1 LB1 spent tl.
Proof.
intros cx Hp kr s1 D ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl mF mdF HB HM HU0 HSAME Lcap Lu Lsk LH Lka
  Lei Lpend Loff Lst Len Lecap HHIST HRS HBUD Hn Hjunk HJF KV KP M24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
fold (dsp0 cx) in Hal16, Hslo, Hshi.
pose proof HRS as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HGSB as (Hg1 & Hg2 & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (_ & HG4096 & HGceil & _).
rewrite RQT in HGceil. unfold AENT, ATABLE in HSAG.
(* the g_s bytes are image bytes (G_DR's first range, HG); no image byte is in the relay table's block *)
assert (HIMG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> YG0d.in_img SEGS x).
{ intros x Hx. refine (proj1 (HG x _)). unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
assert (NT : forall x, YG0d.in_img SEGS x -> ~ (dxSA cx + 24 <= x < dxSA cx + 32)).
{ intros x Hx Hr. destruct (db_img_out_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) x HAR HTB Hx) as (_ & [Hl | Hl]); lia. }
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
assert (HUL : Z.of_nat (length (drain_b_c.ds_u s1)) = re_used e1) by (rewrite <- Lu, db_bzs_len; exact HUlen).
assert (Hcp4 : 4096 + re_used e1 <= re_cap e1) by (unfold ulen in RS_gr; rewrite <- Lcap in RS_gr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [lia|].
assert (Hnle : dnum s1 <= re_cap e1 - re_used e1) by (unfold dnum, ulen; rewrite <- Lcap, HUL; lia).
assert (HNZ : nozero (drain_b_c.ds_u s1)) by (rewrite <- Lu; exact (db_nozero _ HU0)).
(* every byte the representations read: kept *)
assert (KB : forall a, db_out (dxG cx) a -> abyte_kept W1 m1 W1 mF a).
{ intros a (Ha1 & Ha2). split.
  - apply KV; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | unfold DRAIN_FRAME in *; lia | lia].
  - unfold arm. apply writable_kept. exact (KP a). }
assert (KF : forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx ->
  ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W1 mF a).
{ intros a Ha Hn2. split.
  - apply KV; [unfold DRAIN_FRAME in *; lia | unfold DRAIN_FRAME, ESTACK in *; lia | exact Hn2 | lia].
  - unfold arm. apply writable_kept. exact (KP a). }
assert (HSEP : forall b, In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap (dsv cx s1)) out1 ++
  dxrest cx) -> In b (ablocks B ly1 S1) /\ zdisjoint (dxG cx, req_size ATABLE) (fst b, req_size (snd b))).
{ intros b Hb. split; [eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hb]|].
  exact (db_sep_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) _ b HAR Hperm Hb). }
assert (HOKX1 : aentry_okx B ly1 S1 W1 mF e1).
{ apply (db_aentry_okx_kept B RG ly1 S1 W1 m1); [exact HOKX | |].
  - intros r Hr a Ha. apply KB.
    refine (db_aentry_fp_out_x ly1 S1 Hp1 W1 m1 md1 e1 (dxG cx) HAR HOKX _ r Hr a Ha).
    intros b Hb. apply HSEP. apply in_or_app. left. exact Hb.
  - intros b Hb. apply HSEP. apply in_or_app. left. exact Hb. }
assert (HSRC1 : asrc_at B ly1 S1 W1 mF (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1); [exact Hsrc | |].
  - intros r Hr a Ha. apply KB.
    refine (db_asrc_fp_out_x ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) h1 (dxG cx) HAR Hsrc HTB _ _ _ r Hr a Ha);
      [unfold dHA, ASRC in *; lia | unfold dHA, ASRC in *; lia |].
    intros b Hb. apply HSEP. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - intros b Hb. apply HSEP. apply in_or_app. right. apply in_or_app. left. exact Hb. }
pose proof Hout as Hout'.
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF) in Hout';
  [| intros r Hr a Ha; apply KB;
     refine (db_aout_fp_out_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ (dxG cx) HAR Hout HTB _ r Hr a Ha);
     intros b Hb; apply HSEP; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb
   | intros b Hb; apply HSEP; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
unfold DLC_xR, LCORE_xR. cbv zeta.
change (dskp s1 0) with (drain_b_c.ds_skip s1). change (dlH cx s1 0) with (drain_b_c.ds_H s1).
change (dlka cx s1 0) with (drain_b_c.ds_ka s1). change (dloc cx s1 0) with (drain_b_c.ds_ocap s1).
rewrite dm_dlno0. change (drlp s1 0) with (@nil (list Z)). rewrite app_nil_r.
rewrite (dm_drlq0 s1 HNZ).
change (dvirt cx s1 (drain_b_c.ds_skip s1) (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1) (drain_b_c.ds_no s1)
  (drain_b_c.ds_ocap s1)) with (dsv cx s1).
split.
{ (* the memory core *)
  unfold DMEM_xR.
  split; [exact HJF|].
  split.
  { intros a Ha.
    assert (Hai' : YG0d.in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range a Hai') as Hai.
    rewrite KV; [exact (Hrom a Ha) | lia | unfold DRAIN_FRAME, ESTACK in *; lia | unfold DRAIN_FRAME in *; lia
      | exact (NT a Hai')]. }
  split; [intros a Ha1 Ha2 Ha3 Hp'; apply KP; exact (Hpres a Ha1 Ha2 Ha3 Hp')|].
  split; [exact Hframes|].
  split; [exact (db_frame_kept RG HGSB cx W1 m1 W1 mF KF HFR)|].
  split.
  { rewrite (db_entry_split (dr_used e1 (dnum s1))).
    apply (db_garr8_used W1 W1 m1 mF (dxSA cx) e1 (re_used e1 + dnum s1) Hgarr Hpad1 Hpad2); [|lia | exact M24].
    intros x Hx Hn2. apply KV; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | unfold DRAIN_FRAME in *; lia | exact Hn2]. }
  split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 mF); [exact (KP (dxSA cx + i)) | exact (Hawr i Hi)]|].
  split; [apply (db_okx_used B RG HGSB); [exact HOKX1 | lia | lia | lia]|].
  split; [exact HSRC1|].
  split.
  { intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o.
    split; [|split; [|exact Ho]]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx; apply KB;
    apply (db_img_out_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) x HAR HTB); apply HIMG; unfold ASRC in *;
    change (Z.of_nat 4) with 4 in Hx; clear - Hx Hi Hg1 Hg2; lia. }
  split.
  { intros x Hx Hn2. destruct (Hgsk x Hx Hn2) as [A1 A2].
    assert (Hxl : db_out (dxG cx) x) by (apply (db_img_out_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) x HAR HTB); apply HIMG; lia).
    destruct (KB x Hxl) as [B1 B2]. split; [rewrite B1; exact A1 | intros Hw; apply B2; apply A2; exact Hw]. }
  split; [exact Hout'|].
  split; [exact Hlivout | exact Hperm]. }
split.
{ (* the round state the line loop sees *)
  unfold DLINK, dr_used. cbn [re_cap re_U re_skip re_keys re_hp re_kh].
  split; [exact Lcap|].
  split; [rewrite db_bzs_app, Lu, Hjunk; reflexivity|].
  split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|]. split; [exact Lei|].
  split; [exact Lpend|]. split; [exact Loff|]. split; [exact Lst|]. split; [exact Len|]. split; [exact Lecap|].
  exact (dm_dwf_virt RG HGSB cx s1 RS_wf RS_st Hn). }
split; [exact HSAME|].
split; [exact HHIST|].
split; [exact HRS | exact HBUD].
Qed.
(* ---- DROPB over ARx: DDM_x 0x83668 -> s->used += n (0x83684) -> memchr #1 (0x836a4) -> DLL_x (a NUL at q) /
   DLR_x (none), at p = 0.  The entry's Hpe / kr are carried, the cut's Hp1 kept, DDM_x's dbud_x carried. ---- *)
Theorem dr_dropb_xR : dr_dropb_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_dropb_stmt_xR. intros cx Hpe kr s1 D W1 c1 HB HDDM Hdll Hdlr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
unfold DDM_xR in HDDM.
destruct HDDM as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hcfg & Hsp & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R22 & R25 & R26 & R27 &
  HFR & M56 & M64 & M48 & M200 & Hn0 & Hn16 & Hjunk & HMEM & HU0 & HUa & HSAME &
  Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & HHIST & HRS & Hfut & HBUD).
pose proof HFR as HFR'. unfold dr_frame in HFR'. cbv zeta in HFR'.
destruct HFR' as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & HBx10 & HGin0 & HGSA & HSAG & HBrest).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (_ & HG4096 & HGceil & HGia & _).
rewrite RQT in HGceil, HGia. unfold AENT, ATABLE in HSAG.
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld & HND1 & HND2
  & Hkeys).
pose proof HRS as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
assert (HUL : Z.of_nat (length (drain_b_c.ds_u s1)) = re_used e1) by (rewrite <- Lu, db_bzs_len; exact HUlen).
assert (Hcp4 : 4096 + re_used e1 <= re_cap e1) by (unfold ulen in RS_gr; rewrite <- Lcap in RS_gr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (_ & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil.
assert (Hnle : dnum s1 <= re_cap e1 - re_used e1) by (unfold dnum, ulen; rewrite <- Lcap, HUL; lia).
assert (HNZ : nozero (drain_b_c.ds_u s1)) by (rewrite <- Lu; exact (db_nozero _ HU0)).
assert (HdW : bzs (re_U e1 ++ firstn (Z.to_nat (dnum s1)) (re_junk e1)) = dW s1)
  by (unfold dW; rewrite db_bzs_app, Lu, Hjunk; reflexivity).
assert (HLW : Z.of_nat (length (dW s1)) = re_used e1 + dnum s1)
  by (rewrite <- HdW, db_bzs_len, length_app, length_firstn; lia).
assert (HWB : bzs (re_U e1 ++ re_junk e1) = dW s1 ++ bzs (skipn (Z.to_nat (dnum s1)) (re_junk e1))).
{ rewrite <- (firstn_skipn (Z.to_nat (dnum s1)) (re_junk e1)) at 1. rewrite app_assoc, db_bzs_app, HdW. reflexivity. }
assert (HSEPbuf : zdisjoint (dxG cx, req_size ATABLE) (fst (re_buf e1, re_cap e1), req_size (snd (re_buf e1, re_cap e1)))).
{ apply (db_sep_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) _ (re_buf e1, re_cap e1) HAR Hperm).
  apply in_or_app. left. unfold aentry_blks. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by lia. left. reflexivity. }
unfold zdisjoint in HSEPbuf. cbn [fst snd] in HSEPbuf. rewrite RQT, RQC in HSEPbuf.
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
clear memS HJi.
pose proof (db_entry_buf W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MBUF.
pose proof (db_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MUSED.
set (n := dnum s1) in *.
(* ---- the symbolic state at DDM ---- *)
pose proof (db_entry RG W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_used e1) n Hsp
  ltac:(unfold DRAIN_FRAME; lia) ltac:(unfold DRAIN_FRAME; lia)
  ltac:(unfold DRAIN_FRAME; rewrite Zminus_mod, Hal16; reflexivity)
  R27 R26 R21 R19 ltac:(lia) ltac:(lia) ltac:(unfold DB_HI; lia) ltac:(unfold DRAIN_FRAME; lia)
  ltac:(lia) ltac:(lia) F208 F216 F224 MBUF MUSED
  ltac:(intros o' Ho'; apply (apresent_writable SEGS); apply HJpres; unfold DRAIN_FRAME in *; lia) Hawr) as HS.
remember (Eimg (Ereg regs1 (db_extra (dxSA cx) (re_buf e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs1 r).
{ intros n0 r Hn' Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (Usa : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS dbBx DB_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E dbBx 32 (dxSA cx + 16) 16 (dxSA cx) 16 32).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE);
      [exact HAR | exact HTB | lia | rewrite RQT; lia].
  - unfold dbBx. rewrite (U_atom E 21 SB E21) by (unfold SB; lia). reflexivity.
  - apply (U_atom E 32 (dxSA cx) E32). lia.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    rewrite Z.min_l, Z.max_r in Hx by lia. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_join)) with (Z_to_bv 64 (BASE + A_dr_join)).
(* ---- 0x83668 .. 0x836a4: n < 0 / n == 0 refuted, the two shadow checks fold, s->used += n, the call's arguments ---- *)
paj_run_tok_xR RUNR HS HJ SHOK db_Bspan.
{ cbn [ss_mem ss_db db_regions].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  - intros x Hx. cbn [db_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp in Hx.
    left. split; [left; unfold DRAIN_FRAME in *; lia | lia].
  - intros x Hx. cbn [db_ent YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usa in Hx.
    left. split; [|lia]. right. left. split.
    + unfold dFP, dr_fp. apply inFP_cons. left. unfold AENT. lia.
    + exists (dxG cx), ATABLE. split; [exact HTB | rewrite RQT; lia]. }
rename ms into msA.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem msA)) |- _ => rename Hg into GRA end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. db_rreg_x HS (12%bv : bv 5) Q12.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
(* what the run kept: everything but its two write windows *)
assert (KEEP1 : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) ->
  ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W1) (ms_mem msA) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy N1 N2. apply (aview_kept_out E (ss_mem ss_db) (w_H W1) m1 (ms_mem msA) HFr y Hy).
  intros (r & Hin & Hr). cbn [ss_mem ss_db db_regions In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [db_frame db_ent YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?Usp, ?Usa in Hr; lia. }
(* s->used now holds used + n *)
assert (M24 : val_mem SEGS (arm W1 (ms_mem msA)) (dxSA cx + 24) 8 (re_used e1 + n)).
{ replace (re_used e1 + n) with (n + re_used e1) by lia.
  apply (field_of_region E _ 32 (dxSA cx) _ 16 32 24 32 24 8 (SAlu ALU_ADD (SOff 19 0) (SOff 34 0)) _ HR1 Usa).
  - cbn. db_in_x.
  - apply db_den. apply (db_U_add E 19 34 n (re_used e1) E19 E34); lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (Usp1 : spZ (ms_regs msA) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (G10 : getr (ms_regs msA) 10 = w64 (re_buf e1)) by (rewrite Q10; exact E33).
set (nn := re_used e1 + n).
assert (G12 : getr (ms_regs msA) 12 = w64 nn).
{ rewrite Q12. apply db_den. unfold nn. rewrite Z.add_comm. apply (db_U_add E 19 34 n (re_used e1) E19 E34); lia. }
(* the buffer's bytes, as memchr reads them *)
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) (ms_mem msA) (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite KEEP1 by (unfold DRAIN_FRAME in *; lia).
  rewrite (db_garr8_aview W1 m1 (re_buf e1) _ j Hbuf8) by (rewrite db_bzs_len, length_app; lia).
  rewrite HWB, app_nth1 by lia. reflexivity. }
(* the image bytes are off the relay table's block (alx_client_img), so the run kept them *)
assert (ROM1 : rom_view SEGS W1 (ms_mem msA)).
{ intros x Hx.
  assert (Hxi : YG0d.in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range x Hxi) as Hai.
  rewrite KEEP1; [exact (Hrom x Hx) | lia | unfold DRAIN_FRAME in *; lia |].
  intros Hx2. destruct (db_img_out_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) x HAR HTB Hxi) as (_ & [Hl | Hl]); lia. }
assert (SRC : src_ok SEGS W1 (ms_regs msA) (ms_mem msA) (re_buf e1) nn).
{ intros y Hy. split.
  - replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
    rewrite BV by (unfold nn in Hy; lia). discriminate.
  - rewrite Usp1. unfold DRAIN_FRAME, ESTACK in *. lia. }
assert (AMR : amem_range (re_buf e1) nn).
{ pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold nn. rewrite RQC in HBia.
  unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *. lia. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARA.
assert (RA : range_addressable (aview SEGS (w_H W1) (ms_mem msA)) SHADOW_OFF (re_buf e1) nn)
  by (apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ (re_buf e1) (re_cap e1) _ _ HARA Hbin);
      [lia | rewrite RQC; unfold nn; lia]).
assert (HV : 0 < nn -> shadow_hull_vis (aview SEGS (w_H W1) (ms_mem msA)) (re_buf e1) nn)
  by (intros Hnn; apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ (re_buf e1) (re_cap e1) _ _
        HARA Hbin); [lia | rewrite RQC; unfold nn; lia | exact Hnn]).
pose proof (consts_view_of_rom_view SEGS 0x10350 0x10370 W1 (ms_mem msA) HCROM ROM1) as CV.
(* ---- memchr (s->buf, 0, s->used) ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_memchr)
    (fun _ => False)
    (fun regs' (_ : word -> option byte) => exists k, first_byte SEGS W1 (ms_mem msA) (re_buf e1) nn 0 k /\
       getr regs' 10 = (if k <? nn then w64 (re_buf e1 + k) else w64 0))
    W1 (ms_regs msA) (ms_mem msA) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5052)) HG eq_refl HJ).
  - rewrite Usp1. lia.
  - rewrite HDF. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros _. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE _. eapply SRr_mono.
    { exact (AMEMCHR ly1 S1 Hp1 W1 (ms_regs msA) (ms_mem msA) _ (re_buf e1) 0 nn HPRE G10 Q11 G12
        ltac:(lia) ltac:(unfold nn; lia) ltac:(lia) ltac:(unfold nn; lia) SRC AMR RA HV CV). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Hres) & Hfr2 & Hpres2).
(* ---- after the call: the frame region kept, the caller-saved registers havocked from atom 35 ---- *)
assert (KR : region_kept SEGS E (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) mem2) db_frame).
{ apply (region_kept_aview E (w_H W1) (ms_mem msA) mem2 2 (dsp0 cx - DRAIN_FRAME) 192 232 192 200 _ Usp).
  - intros y Hy. apply Hfr2; [lia | intros Hf; exact Hf | unfold DRAIN_FRAME, ESTACK in *; lia].
  - exact Hpres2. }
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
specialize (HS2 ltac:(constructor; [exact KR | constructor])).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (SHOK2 : sh_ok SEGS dbBx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
assert (Usp2 : bv_unsigned (ew Ea 2) = dsp0 cx + - DRAIN_FRAME) by (rewrite (OLDa 2%nat ltac:(lia)), Usp; lia).
(* ---- 0x836a8 .. 0x836b8: s7 = the result, 192(sp) = (SA + 8) >> 3, the beqz ---- *)
paj_run_tok_xR RUNR HS HJ2 SHOK2 db_Bspan. { apply awr_ok_x_of0. db_awr_frame_x Usp2. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFrB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hg into GRB end.
assert (KEEPB : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W1) (ms_mem msB) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy N1 N2 N3.
  rewrite (aview_kept_out Ea _ (w_H W1) mem2 (ms_mem msB) HFrB y Hy).
  - rewrite (Hfr2 y Hy (fun Hf => Hf) ltac:(unfold DRAIN_FRAME, ESTACK in *; lia)). exact (KEEP1 y Hy N2 N3).
  - intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia. }
assert (PRESB : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msB) y).
{ intros y Hp. apply (apresent_grows _ _ _ _ GRB). apply Hpres2. exact (apresent_grows _ _ _ _ GRA Hp). }
assert (M24B : val_mem SEGS (arm W1 (ms_mem msB)) (dxSA cx + 24) 8 (re_used e1 + n)).
{ apply (akept_vm W1 (ms_mem msA)); [|exact M24]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. split.
  - rewrite (aview_kept_out Ea _ (w_H W1) mem2 (ms_mem msB) HFrB x ltac:(lia)).
    + apply Hfr2; [lia | intros Hf; exact Hf | unfold DRAIN_FRAME, ESTACK in *; lia].
    + intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia.
  - intros Hw. unfold arm. apply (writable_kept (w_H W1) (ms_mem msA) (ms_mem msB)); [|exact Hw]. intros Hp.
    apply (apresent_grows _ _ _ _ GRB). apply Hpres2. exact Hp. }
set (a0v := if kk <? nn then re_buf e1 + kk else 0).
assert (HA0 : ew Ea 39 = Z_to_bv 64 a0v) by (rewrite <- R10b, Hres; unfold a0v; destruct (kk <? nn); reflexivity).
destruct Hfb as (Hk0 & Hkb & Hkz).
assert (Ra0 : 0 <= a0v < 2 ^ 64) by (unfold a0v, nn in *; destruct (kk <? re_used e1 + n); lia).
psrr_branch_tok RUNR BRR HS SHOK2 db_Bspan.
- (* s7 = 0: no NUL in the buffer; 0x83a48 mv s10, s8; DLR_x with p = 0 *)
  rewrite branch_eq_U, (U_atom Ea 39 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk = nn).
  { destruct (Z_lt_ge_dec kk nn) as [Hl | Hl]; [|lia]. exfalso. unfold a0v in Hc.
    rewrite (proj2 (Z.ltb_lt kk nn) Hl) in Hc. apply Z.eqb_eq in Hc. lia. }
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 db_Bspan A_dr_rest. { apply awr_ok_x_of0. db_awr_frame_x Usp2. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hg into GRF end.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRF. cbn [ms_mem restrict] in HRF.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (24%bv : bv 5) P24r. db_rreg_x HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy N1 N2 N3. rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF y Hy).
    - exact (KEEPB y Hy N1 N2 N3).
    - intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia. }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ _ GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hn2. split; [apply KEEPF; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | exact Hn2 | lia]|].
    unfold arm. apply (writable_kept (w_H W1) m1 (ms_mem msF)). exact (PRESF y). }
  assert (M24F : val_mem SEGS (arm W1 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + n)).
  { apply (akept_vm W1 (ms_mem msB)); [|exact M24B]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. split.
    - rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF x ltac:(lia)); [reflexivity|].
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia.
    - intros Hw. unfold arm. apply (writable_kept (w_H W1) (ms_mem msB) (ms_mem msF)); [|exact Hw]. intros Hp.
      exact (apresent_grows _ _ _ _ GRF Hp). }
  assert (M192F : val_mem SEGS (arm W1 (ms_mem msF)) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8)).
  { apply (slot_of_region Ea _ _ _ _ _ _ _ 192 (SAlu ALU_SRL (SOff 32 8) (SLit 3)) _ HRF).
    - rewrite Usp2. lia.
    - cbn. db_in_x.
    - apply db_den. apply (db_U_srl Ea 32 (dxSA cx) 8); [rewrite (OLDa 32%nat ltac:(lia)); exact E32 | lia | lia].
    - pose proof (db_div8 (dxSA cx + 8) ltac:(lia)). lia. }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdlr W1). unfold DLR_xR.
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF), mdF, k1, (dr_used e1 n), h1, out1, ev1, LB1, spent, jb, a, o, ha, ks,
    tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (db_dregs RG HGSB cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hsp R3 R4 R22 R27 R18 R9 R8 R21 HFR M200 M56 M48
      M64);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity]
      | apply (RK _ 9%nat P9); [lia | reflexivity] | apply (RK _ 8%nat P8); [lia | reflexivity]
      | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF | exact M192F ].
    rewrite P27, (OLDa 32%nat ltac:(lia)), E32, R27. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  split; [rewrite P24r, (OLDa 33%nat ltac:(lia)), E33; unfold w64; f_equal; cbn [re_buf dr_used]; lia|].
  split.
  { rewrite P25. apply db_den. rewrite Nat.sub_0_r, HLW, Z.add_comm.
    apply (db_U_add Ea 19 34 n (re_used e1));
      [rewrite (OLDa 19%nat ltac:(lia)); exact E19 | rewrite (OLDa 34%nat ltac:(lia)); exact E34 | lia | lia | lia]. }
  split; [rewrite P26, (OLDa 33%nat ltac:(lia)), E33; reflexivity|].
  split; [apply (dm_dbound0 RG)|].
  split.
  { intros i Hi. destruct (Nat.lt_ge_cases i (length (dW s1))) as [Hil | Hil].
    - destruct (Hkb (Z.of_nat i) ltac:(lia)) as (bb & Hb & Hb0).
      rewrite BV in Hb by exact Hil. injection Hb as <-.
      rewrite (nth_error_nth' (dW s1) 0) by exact Hil.
      intros Hn0'. injection Hn0' as Hn0'. exact (Hb0 Hn0').
    - rewrite (proj2 (nth_error_None (dW s1) i) Hil). discriminate. }
  split.
  { exact (db_dlc_xR cx Hpe kr s1 D ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF HB HMEM HU0
      HSAME Lcap Lu Lsk LH Lka Lei Lpend Loff Lst Len Lecap HHIST HRS HBUD Hn0 Hjunk HJ2 KEEPF PRESF M24F). }
  rewrite dm_dlno0, (dm_drlq0 s1 HNZ). exact Hfut.
- (* s7 <> 0: the first NUL at s->buf + kk; DLL_x with p = 0, q = kk *)
  rewrite branch_eq_U, (U_atom Ea 39 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk < nn).
  { destruct (Z_lt_ge_dec kk nn) as [Hl | Hl]; [exact Hl|]. exfalso. unfold a0v in Hc.
    rewrite (proj2 (Z.ltb_ge kk nn) ltac:(lia)) in Hc. cbn in Hc. discriminate Hc. }
  assert (Ha0 : a0v = re_buf e1 + kk) by (unfold a0v; rewrite (proj2 (Z.ltb_lt kk nn) Hkk); reflexivity).
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 db_Bspan A_dr_line. { apply awr_ok_x_of0. db_awr_frame_x Usp2. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
    rename Hg into GRF end.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRF. cbn [ms_mem restrict] in HRF.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24r. prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy N1 N2 N3. rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF y Hy).
    - exact (KEEPB y Hy N1 N2 N3).
    - intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia. }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ _ GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx ->
    ~ (dsp0 cx - DRAIN_FRAME + 192 <= y < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hn2. split; [apply KEEPF; [lia | unfold DRAIN_FRAME, ESTACK in *; lia | exact Hn2 | lia]|].
    unfold arm. apply (writable_kept (w_H W1) m1 (ms_mem msF)). exact (PRESF y). }
  assert (M24F : val_mem SEGS (arm W1 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + n)).
  { apply (akept_vm W1 (ms_mem msB)); [|exact M24B]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. split.
    - rewrite (aview_kept_out Ea _ (w_H W1) (ms_mem msB) (ms_mem msF) HFrF x ltac:(lia)); [reflexivity|].
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp2 in Hr. lia.
    - intros Hw. unfold arm. apply (writable_kept (w_H W1) (ms_mem msB) (ms_mem msF)); [|exact Hw]. intros Hp.
      exact (apresent_grows _ _ _ _ GRF Hp). }
  assert (M192F : val_mem SEGS (arm W1 (ms_mem msF)) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8)).
  { apply (slot_of_region Ea _ _ _ _ _ _ _ 192 (SAlu ALU_SRL (SOff 32 8) (SLit 3)) _ HRF).
    - rewrite Usp2. lia.
    - cbn. db_in_x.
    - apply db_den. apply (db_U_srl Ea 32 (dxSA cx) 8); [rewrite (OLDa 32%nat ltac:(lia)); exact E32 | lia | lia].
    - pose proof (db_div8 (dxSA cx + 8) ltac:(lia)). lia. }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdll (Z.to_nat kk) W1). unfold DLL_xR.
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF), mdF, k1, (dr_used e1 n), h1, out1, ev1, LB1, spent, jb, a, o, ha, ks,
    tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (db_dregs RG HGSB cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hsp R3 R4 R22 R27 R18 R9 R8 R21 HFR M200 M56 M48
      M64);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity]
      | apply (RK _ 9%nat P9); [lia | reflexivity] | apply (RK _ 8%nat P8); [lia | reflexivity]
      | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF | exact M192F ].
    rewrite P27, (OLDa 32%nat ltac:(lia)), E32, R27. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  split; [rewrite P23, HA0, Ha0; unfold w64; f_equal; cbn [re_buf dr_used]; lia|].
  split; [rewrite P24r, (OLDa 33%nat ltac:(lia)), E33; unfold w64; f_equal; cbn [re_buf dr_used]; lia|].
  split; [apply (dm_dbound0 RG)|].
  split; [lia|].
  split.
  { pose proof (Hkz Hkk) as Hz.
    replace (re_buf e1 + kk) with (re_buf e1 + Z.of_nat (Z.to_nat kk)) in Hz by lia.
    rewrite BV in Hz by lia. injection Hz as Hz.
    rewrite (nth_error_nth' (dW s1) 0) by lia. rewrite Hz. reflexivity. }
  split.
  { intros i Hi. destruct (Hkb (Z.of_nat i) ltac:(lia)) as (bb & Hb & Hb0).
    rewrite BV in Hb by lia. injection Hb as <-.
    rewrite (nth_error_nth' (dW s1) 0) by lia.
    intros Hn0'. injection Hn0' as Hn0'. exact (Hb0 Hn0'). }
  split.
  { exact (db_dlc_xR cx Hpe kr s1 D ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF HB HMEM HU0
      HSAME Lcap Lu Lsk LH Lka Lei Lpend Loff Lst Len Lecap HHIST HRS HBUD Hn0 Hjunk HJ2 KEEPF PRESF M24F). }
  rewrite dm_dlno0, (dm_drlq0 s1 HNZ). exact Hfut.
Qed.
End wR.


(* ---- db_dlc: the line loop's core at its first cut, from DDM_x's, in the memory the segment leaves. ---- *)
Lemma db_dlc_x : forall cx Hp kr s1 D ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl mF mdF,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> DSAME cx e1 h1 ->
re_cap e1 = drain_b_c.ds_cap s1 -> bzs (re_U e1) = drain_b_c.ds_u s1 ->
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) ->
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 -> drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 ->
hs_eintr h1 = 0 ->
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend (dnext (dlive cx) (dxmx cx) s1) ->
hs_off h1 = drain_b_c.ds_off (dnext (dlive cx) (dxmx cx) s1) ->
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) ->
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) ->
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) ->
DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1
  (Z.of_nat (length (drl s1))) ->
RSTART cx s1 D -> dbud_x B MT RP MMAX cx kr ly1 S1 spent tl ->
0 < dnum s1 -> bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
   ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) -> ~ (dxSA cx + 24 <= a < dxSA cx + 32) ->
   aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
val_mem SEGS (arm W1 mF) (dxSA cx + 24) 8 (re_used e1 + dnum s1) ->
DLC_x B PST ARx MT RP MMAX RG cx Hp kr s1 D 0 ly1 S1 Hp1 W1 mF mdF k1 (dr_used e1 (dnum s1)) h1 out1 ev1 LB1 spent tl.
Proof. eapply (db_dlc_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- DROPB over ARx: DDM_x 0x83668 -> s->used += n (0x83684) -> memchr #1 (0x836a4) -> DLL_x (a NUL at q) /
   DLR_x (none), at p = 0.  The entry's Hpe / kr are carried, the cut's Hp1 kept, DDM_x's dbud_x carried. ---- *)
Theorem dr_dropb_x : dr_dropb_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_dropb_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.
End cx.
End bx.
End ax.
