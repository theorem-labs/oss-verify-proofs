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
(* ARx form (route (b), step 3): Section cx proves dr_next_x, W_drain_cx_x.v's dr_next_stmt_x at the room texts, over
   any allocator relation ARx, its journal at W_contract_x.v's DRAIN_STK_x; the AR walk dr_next (Section c) is unchanged. *)
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
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
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

(* ---- Byte helpers (W_gsbytes_scratch.v's gs_*, ported). ---- *)
Lemma dn_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma dn_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma dn_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.

Lemma dn_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma dn_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, dn_nth_zle by exact Hk. rewrite dn_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma dn_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.

Lemma dn_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite dn_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite dn_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma dn_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Ltac dn_len := rewrite ?length_app, ?dn_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].

(* RelayRep.v entry_bytes: fd, eof, skip (4 each), pad1 (4), buf at + 16, used at + 24, cap, hp, nheld, pad2. *)
Lemma dn_entry_buf : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_buf e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 16) 8 (re_buf e).
Proof.
intros W m SA e Hp1 Hb H.
unfold entry_bytes in H. rewrite !dn_bzs_app, !app_assoc in H.
do 5 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dn_le8_bytes (re_buf e) Hb) in H.
apply (dn_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hb|].
apply (dn_garr8_at _ _ _ _ H). dn_len. lia.
Qed.

Lemma dn_entry_used : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_used e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 24) 8 (re_used e).
Proof.
intros W m SA e Hp1 Hb H.
unfold entry_bytes in H. rewrite !dn_bzs_app, !app_assoc in H.
do 4 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dn_le8_bytes (re_used e) Hb) in H.
apply (dn_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hb|].
apply (dn_garr8_at _ _ _ _ H). dn_len. lia.
Qed.

Lemma dn_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (bzs (entry_bytes e)) = 56%nat.
Proof. intros e H1 H2. unfold entry_bytes. rewrite dn_bzs_len, !length_app, H1, H2, !Mem.length_le8, !Mem.length_le4. reflexivity. Qed.

(* ---- Symbolic values (W_drain_pro.v's pro_den / pro_U_srl / pro_U_shadow). ---- *)
Lemma dn_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma dn_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma dn_U_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SB ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0)) = SHADOW_OFF + (v + c) / 8.
Proof.
intros E n v c Hn H32 Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (dn_U_srl E n v c Hn Hv Hc), (U_atom E 32 SB H32) by (unfold SB; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by
  (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
replace (SB) with SHADOW_OFF by reflexivity.
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma dn_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma dn_shadow_range : forall a, 0 <= a < 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64.
Proof.
intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono a (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in *. lia.
Qed.

(* memchr's length argument as the walk computes it: (s->buf - (s7 + 1)) + s->used with s7 = s->buf + p - 1 *)
Lemma dn_U_len : forall E (s7 buf used p : Z),
ew E 23 = Z_to_bv 64 s7 -> ew E 34 = Z_to_bv 64 buf -> ew E 35 = Z_to_bv 64 used ->
0 <= s7 < 2 ^ 64 -> 0 <= buf < 2 ^ 64 -> 0 <= used < 2 ^ 64 -> s7 = buf + p - 1 -> 0 <= used - p < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 23 0) (SLit 18446744073709551615)) (SLit (-1)))
  (SOff 34 0)) (SOff 35 0)) = used - p.
Proof.
intros E s7 buf used p H23 H34 H35 R7 Rb Ru Hs Hn.
rewrite !U_SAlu, U_SMd, !U_SLit, (U_atom E 23 s7 H23 R7), (U_atom E 34 buf H34 Rb), (U_atom E 35 used H35 Ru).
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r by lia.
change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615.
rewrite <- Z.add_assoc, Z.add_mod_idemp_l by lia.
match goal with |- ?X mod ?M = _ => assert (EX : X = (used - p) + (buf + p - 1) * M) by (subst s7; lia); rewrite EX end.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* a byte of a garr8 run, as the ASan view reads it *)
Lemma dn_garr8_aview : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j H Hj. unfold aview. pose proof (proj2 (H j Hj)) as Hr.
unfold arm in H. rewrite (garr8_mbyte SEGS (mrestrict (w_H W) m) base l j H Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

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
(* the walk's globals, the allocator's statics, errno and the sink's overflow head are never read-only image
   bytes: what a callee's journal may change is disjoint from ROM, so rom_view survives it (W_journal.v
   rom_out / ajournal_gx_rom_view).  The pinned placement decides it by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
(* memchr: the shared general text (dis-7's amemchr_realizesM, lib/Rt/MemchrDef.v; proved on our image by R3 as
   memchr_icpt_realizesM): both drain sites scan inside one live block's requested size for all n bytes.
   Its constant window is the musl memchr's masks at 0x10350 .. 0x10370, read-only image bytes (HCROM). *)
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
(* the allocator instance's granule-tail fact (Main's ALLOC_TAIL): the rest of a live block's last 8-byte
   granule is mapped (the chunk is 8-aligned and rounded up to a granule). *)
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program: send_line (W7) and list_push (W2, in its G-generic form; drain
   instantiates it at list_push's own globals, the 16 bytes of h->expected at HA + 64, and lifts the callee's
   journal to G_DR with ajournal_gx_G_mono) *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts: errno is tp - 164 (W_sites.v aerrno_realizes) and its 4 bytes have zero shadow *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
(* the 4 * 96 bytes of g_s are a zero-shadow range of the image (a plain global, no redzone between the slots) *)
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
(* placement: g_s is reached by PAddHi (A_OBJ 22), so no rebase is needed for it *)
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
(* the string literals of gesture_seen, in .rodata (W_drain_cx.v dlit_at) *)
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
(* placement: the cells drain reads or writes are pairwise disjoint *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
(* g_s lies in the image band (the walk computes shadow addresses of its fields) *)
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
(* the instance's request bound *)
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
(* placement of the three output cells aout_at reads that are not in G_DR's g_s range (W_drain_cx.v HV9 / HV12 / HSM) *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- What the call leaves.  memchr writes nothing outside its scratch [sp - ESTACK, sp); every byte the cut's
   representations read lies below alloc_ceiling (a live block, the image) or in drain's frame [sp, sp + 336),
   so the cut's memory core moves to the memory after the call (W_drain_pro.v's pro_*_low, without key slack). *)
Ltac dn_in := repeat (first [left; reflexivity | right]).
Definition dn_low (a : Z) : Prop := 0 <= a < alloc_ceiling.

Lemma dn_blk_low : forall ly S (W : world SEGS) mem md q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a < q + req_size n -> dn_low a.
Proof.
intros ly S W mem md q n a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
unfold dn_low. lia.
Qed.

Lemma dn_img_low : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= 0x5fb000 -> dn_low a.
Proof.
intros a lo hi H1 H2 H3 H4. pose proof (@ASAN_CEIL_range rc) as (HC & _). unfold ASAN_CEIL in HC. unfold dn_low. lia.
Qed.

Lemma dn_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dn_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dn_aentry_fp_low : forall ly S (W : world SEGS) mem md e,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & Hle & Hbuf & _ & Hhp & _ & _ & Hks).
assert (KH : In r (gfp (re_hp e) (bzs (key_ptrs (re_keys e))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e)) -> dn_low a).
{ intros Hr'. destruct Hr' as [<- | Hr'].
  - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite dn_bzs_len, dn_key_ptrs_len in Ha.
    destruct Hhp as [(Hz & Hke) | (Hz & Hin & Hk1 & Hk2 & _)].
    + rewrite Hke in Ha. cbn [length] in Ha. lia.
    + apply (dn_blk_low ly S W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
      pose proof (dn_req_ge (re_kh e)). unfold re_nheld in Hk1. lia.
  - apply in_map_iff in Hr' as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite dn_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    apply (dn_blk_low ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
    pose proof (dn_req_ge (Z.of_nat (length (key_text k)) + 1)). lia. }
unfold aentry_fp in Hr. destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; cbn [app] in Hr.
- exact (KH Hr).
- destruct Hr as [<- | Hr]; [|exact (KH Hr)].
  unfold gfp in Ha. cbn [fst snd] in Ha. rewrite dn_bzs_len, length_app in Ha.
  destruct Hbuf as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
  apply (dn_blk_low ly S W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
  pose proof (dn_req_ge (re_cap e)). lia.
Qed.

Lemma dn_alist_fp_low : forall ly S (W : world SEGS) mem md LA l lines lo hi,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dn_img_low a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite dn_bzs_len, length_app, dn_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (dn_blk_low ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (dn_req_ge (AREC * hl_cap l)) as Hrq.
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite dn_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (dn_blk_low ly S W mem md (fst q) (Z.of_nat (length (snd q)) + 1) a HAR Hin); [lia|].
    pose proof (dn_req_ge (Z.of_nat (length (snd q)) + 1)). lia.
Qed.

Lemma dn_asrc_fp_low : forall ly S (W : world SEGS) mem md HA h,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dn_img_low a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite dn_bzs_len in Ha.
  apply (dn_blk_low ly S W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (dn_req_ge APARTIAL). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (dn_alist_fp_low ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (dn_alist_fp_low ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
    * refine (dn_alist_fp_low ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
Qed.

Lemma dn_aout_fp_low : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (@ASAN_CEIL_range rc) as (HC & _). unfold ASAN_CEIL in HC.
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> dn_low a).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI). unfold dn_low, kLowMemEnd in *. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (dn_img_low a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; dn_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; dn_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; dn_in | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (dn_img_low a (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; dn_in | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (dn_img_low a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; dn_in | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; dn_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (dn_blk_low ly S W mem md out cap a HAR Hin); [lia|].
  pose proof (dn_req_ge cap). lia.
Qed.

(* W_drain_gs.v gs_aentry_okx_kept (W_rep.v aentry_ok_kept for aentry_okx), ported *)
Lemma dn_aentry_okx_kept : forall ly S W mem ly' S' W' mem' e,
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

(* drain's frame: every slot lies in [sp, sp + 336) *)
Lemma dn_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
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

(* the cut's memory core, moved across a step that keeps every byte outside [sp - ESTACK, sp) *)
Lemma dn_dmem_kept : forall cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 m2 md2,
alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE -> (dxj cx < 4)%nat ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM B RG cx ly1 S1 W1 m2 md2 k1 e1 h1 s out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 m2 md2 Hst Htop HG1 HG2 Hj HM HJ2 KV KP.
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HGSB as (Hg1 & Hg2 & _).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
  abyte_kept W1 m1 W1 m2 a).
{ intros a Ha Hn. split; [exact (KV a Ha Hn)|]. unfold arm. apply writable_kept. exact (KP a). }
assert (KL : forall a, dn_low a -> abyte_kept W1 m1 W1 m2 a)
  by (intros a Ha; unfold dn_low in Ha; apply KB; [clear - Ha Hst Htop HES HDF; lia | clear - Ha Hst HES HDF; lia]).
pose proof (@ASAN_CEIL_range rc) as (HC & _). unfold ASAN_CEIL in HC.
assert (KF : forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W1 m1 W1 m2 a)
  by (intros a Ha; apply KB; [clear - Ha Hst Htop HES HDF HC; lia | clear - Ha; lia]).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (SAL : forall a, dxSA cx <= a < dxSA cx + AENT -> dn_low a).
{ intros a Ha. apply (dn_blk_low ly1 S1 W1 m1 md1 (dxG cx) ATABLE a HAR HTB); [lia|].
  pose proof (dn_req_ge ATABLE). lia. }
assert (INB : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1))
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _).
unfold DMEM.
split; [exact HJ2|].
split.
{ intros a Ha.
  assert (Hai : 65536 <= a < 6270976)
    by (destruct Ha as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite KV; [exact (Hrom a Ha) | clear - Hai; lia | clear - Hai Hst HC HES HDF; lia]. }
split; [intros a Ha1 Ha2 Ha3 Hp; apply KP; exact (Hpres a Ha1 Ha2 Ha3 Hp)|].
split; [exact Hframes|].
split; [exact (dn_frame_kept cx W1 m1 W1 m2 KF HFR)|].
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx. apply KL. apply SAL.
  rewrite (dn_entry_len e1 Hpad1 Hpad2) in Hx. unfold AENT. lia. }
split; [apply (akept_awr W1 m1); [intros x Hx; apply KL; apply SAL; exact Hx | exact Hawr]|].
split.
{ apply (dn_aentry_okx_kept ly1 S1 W1 m1); [exact HOKX | | intros b Hb; apply INB; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KL. exact (dn_aentry_fp_low ly1 S1 W1 m1 md1 e1 HAR HOKX r Hr x Hx). }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1); [exact Hsrc | |
    intros b Hb; apply INB; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KL.
  refine (dn_asrc_fp_low ly1 S1 W1 m1 md1 (dHA RG cx) h1 HAR Hsrc _ _ r Hr x Hx);
  unfold dHA, ASRC in *; clear - Hj; nia. }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o.
  split; [|split; [|exact Ho]]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx; apply KL;
  apply (dn_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; cbn in Hx; clear - Hx Hi Hg1 Hg2; nia. }
split.
{ intros x Hx Hn. destruct (Hgsk x Hx Hn) as [A1 A2].
  assert (Hxl : dn_low x) by (apply (dn_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia).
  destruct (KL x Hxl) as [B1 B2]. split; [rewrite B1; exact A1 | intros Hw; apply B2; apply A2; exact Hw]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1); [exact Hout | |
    intros b Hb; apply INB; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KL. exact (dn_aout_fp_low ly1 S1 W1 m1 md1 _ _ _ _ _ _ HAR Hout r Hr x Hx). }
split; [exact Hlivout | exact Hperm].
Qed.

Lemma dn_dlc_kept : forall cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2,
alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE -> (dxj cx < 4)%nat ->
DLC B MT MMAX RG cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DLC B MT MMAX RG cx s1 D p ly1 S1 W1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 Hst Htop HG1 HG2 Hj HD HJ2 KV KP.
unfold DLC, LCORE in *. destruct HD as (HM & HR). split; [|exact HR].
exact (dn_dmem_kept cx _ _ _ _ _ _ _ _ _ _ _ _ _ m2 md2 Hst Htop HG1 HG2 Hj HM HJ2 KV KP).
Qed.

(* the line loop's registers and frame slots, moved to a state that keeps the nine registers and the frame *)
Lemma dn_dregs_kept : forall cx regs regs' (W : world SEGS) m m',
dregs_line RG cx regs W m ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 22 = getr regs 22 -> getr regs' 27 = getr regs 27 -> getr regs' 18 = getr regs 18 ->
getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 -> getr regs' 21 = getr regs 21 ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W m' a) ->
dregs_line RG cx regs' W m'.
Proof.
intros cx regs regs' W m m' HR E2 E3 E4 E22 E27 E18 E9 E8 E21 KF.
destruct HR as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
unfold dregs_line. unfold spZ in *. rewrite E2, E3, E4, E22, E27, E18, E9, E8, E21.
do 9 (split; [assumption|]).
split; [exact (dn_frame_kept cx W m W m' KF HFR)|].
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
apply V; [lia | lia | assumption].
Qed.

(* a run whose symbolic state has no region writes nothing *)
Lemma dn_frame_nil : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> rs = [] ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hn a Ha. apply (aview_kept_out E rs H m m' HF a Ha). subst rs. intros (r & Hin & _). destruct Hin.
Qed.

(* ---- The symbolic state at DLN (0x836f4). ----
   Atoms beyond the 32 registers: 32 = the shadow base SB (Bx), 33 = SA (the relay entry), 34 = s->buf,
   35 = s->used.  s11 is pinned to SA + 24.  The walk loads 224(sp) = shadow (SA + 24), 216(sp) = shadow (SA + 16)
   and 200(sp) = SA + 16 (the two shadow slots in the SAlu shadow form, so that tok_load folds the two shadow
   checks: [SA + 16, SA + 32) is addressable, DN_SH), then s->buf and s->used.  No region has a write window. *)
Definition Bx : sv := SOff 32 0.
Definition DN_HI : Z := 140737479966720.
Definition dn_regs : list sv := sr_set sr_atoms 27%bv (SOff 33 24).
Definition dn_frame : YP09.region := YP09.mkRegion (Some 2%nat) 200 232 200 200
  [ YP09.mkChunk 200 (CVal 8 (SOff 33 16));
    YP09.mkChunk 216 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 16) (SLit 3)) (SOff 32 0)));
    YP09.mkChunk 224 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 24) (SLit 3)) (SOff 32 0))) ].
Definition dn_ent : YP09.region := YP09.mkRegion (Some 33%nat) 16 32 16 16
  [ YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0)) ].
Definition dn_regions : smem := [ dn_frame; dn_ent ].
Definition dn_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 DN_HI 0) ] [] [].
Definition ss_dn : sstate := mkSS A_dr_next dn_regs dn_regions None dn_facts.
Definition DN_SH : list shent := [ mkSHE 33 16 32 ].
Definition dn_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition dn_extra (SA BUF USED : Z) : list word := map (Z_to_bv 64) [SB; SA; BUF; USED].

Lemma dn_entry : forall (W : world SEGS) regs1 m1 sp SA BUF USED,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 27 = w64 (SA + 24) -> 4096 <= SA -> SA + 32 <= DN_HI -> SA + 32 <= sp ->
0 <= BUF < 2 ^ 64 -> 0 <= USED < 2 ^ 64 ->
val_mem SEGS (arm W m1) (sp + 200) 8 (SA + 16) ->
val_mem SEGS (arm W m1) (sp + 216) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W m1) (sp + 224) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W m1) (SA + 16) 8 BUF ->
val_mem SEGS (arm W m1) (SA + 24) 8 USED ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dn_extra SA BUF USED))) ss_dn
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_next)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 sp SA BUF USED Hsp Hlo Hhi Hal R27 HSA1 HSA2 HSA3 HBUF HUSED M200 M216 M224 MBUF MUSED.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (dn_extra SA BUF USED))).
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 BUF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 USED) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (Usa : bv_unsigned (ew E 33) = SA) by (rewrite E33; apply unsigned_lit_small; unfold DN_HI in *; lia).
unfold DN_HI in HSA2. unfold DRAIN_FRAME in Hhi.
unfold ss_dn. apply pa_entry_st_ok_full.
- unfold dn_regs. apply regs_ok_pin;
    [ | intros X; discriminate X
    | rewrite (den_atom E 33%nat SA 24 E33) by lia; exact R27 ].
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dn_regions, dn_frame, dn_ent.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?Usa.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 200 8 (SOff 33 16) (SA + 16));
      [rewrite (den_atom E 33%nat SA 16 E33) by lia; reflexivity | cbn; lia | cbn; lia | exact M200].
    * apply (chunk_ok_val SEGS E _ sp 216 8 _ (shadow_addr (SA + 16)));
      [apply dn_den; rewrite (dn_U_shadow E 33 SA 16 E33 E32) by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply dn_shadow_range; lia
      | cbn; lia | exact M216].
    * apply (chunk_ok_val SEGS E _ sp 224 8 _ (shadow_addr (SA + 24)));
      [apply dn_den; rewrite (dn_U_shadow E 33 SA 24 E33 E32) by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply dn_shadow_range; lia
      | cbn; lia | exact M224].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ SA 16 8 (SOff 34 0) BUF);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact MBUF].
    * apply (chunk_ok_val SEGS E _ SA 24 8 (SOff 35 0) USED);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact MUSED].
- apply pairwise_disjoint_of_extents. unfold dn_regions, dn_frame, dn_ent, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usa.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [dn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usa, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, DN_HI. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* ---- NEXT: DLN 0x836f4 -> memchr #2 (0x8372c) -> DLL (a NUL at q) / DLR (none). ---- *)
Theorem dr_next : dr_next_stmt B MT MMAX RG.
Proof.
unfold dr_next_stmt. intros cx s1 D p W1 c1 HB HDLN Hdll Hdlr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
unfold DLN in HDLN.
destruct HDLN as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl
  & Hcfg & Hregs & H23 & Hbound & Hp0 & HDLC & Hdlfut).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsaved).
pose proof HDLC as HDLC'. unfold DLC, LCORE in HDLC'.
destruct HDLC' as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & HBx10 & Htbl & HSAlo & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *.
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
assert (HUW : bzs (re_U e1) = dW s1).
{ destruct HLINK as (_ & HU & _). unfold dvirt in HU. cbn [drain_b_c.ds_u] in HU. exact HU. }
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, dn_bzs_len; lia).
assert (Hcapb : re_cap e1 <= 16384) by (clear - Hcapr; destruct Hcapr as [Hq | [Hq | Hq]]; lia).
pose proof Hbound as HBD. destruct Hbound as (Hpl & Hpz). clear Hpz Heof Hskip Hcapr Hheld.
assert (Hcap0 : re_cap e1 <> 0) by (intros Hc; rewrite Hc in Husedr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & HBpres & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil.
(* the entry's two cells *)
pose proof (dn_entry_buf W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MBUF.
pose proof (dn_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MUSED.
(* the symbolic state *)
pose proof (dn_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_used e1) Hsp
  ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity) R27 ltac:(lia) ltac:(unfold DN_HI; lia)
  ltac:(lia) ltac:(lia) ltac:(lia) M200 F216 F224 MBUF MUSED) as HS.
remember (Eimg (Ereg regs1 (dn_extra (dxSA cx) (re_buf e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (dn_extra (dxSA cx) (re_buf e1) (re_used e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_used e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (SHOK : sh_ok SEGS Bx DN_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E Bx 33 (dxSA cx + 16) 16 (dxSA cx) 16 32).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE); [exact HAR | exact HTB | lia | unfold ATABLE; rewrite RQT; lia].
  - unfold Bx. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). reflexivity.
  - apply (U_atom E 33 (dxSA cx) E33). lia.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    rewrite Z.min_l, Z.max_r in Hx by lia. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_next)) with (Z_to_bv 64 (BASE + A_dr_next)).
paj_run_tok RUN HS HJ SHOK dn_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
(* the run before the call wrote nothing *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_dn dn_regions In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi dn_frame dn_ent] in Hr; lia. }
assert (HARm : AR SEGS B ly1 S1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR; exact HJ).
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros x Hx. rewrite KEEP1; [exact (Hrom x Hx)|].
  destruct Hx as (sg & Hsg & _ & Hr). pose proof (pa_img_range x ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
(* memchr (s->buf + p, 0, s->used - p) *)
set (x := re_buf e1 + Z.of_nat p). set (n := re_used e1 - Z.of_nat p).
assert (Hxn : 4096 <= x /\ 0 <= n /\ x + n = re_buf e1 + re_used e1) by (unfold x, n; lia).
assert (Usp1 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (G10 : getr (ms_regs ms) 10 = w64 x).
{ rewrite Q10, (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. unfold w64.
  rewrite unsigned_lit_small by lia. f_equal. unfold x. lia. }
assert (G12 : getr (ms_regs ms) 12 = w64 n).
{ rewrite Q12.
  transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 23 0)
    (SLit 18446744073709551615)) (SLit (-1))) (SOff 34 0)) (SOff 35 0))).
  { cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
  rewrite denot_lit_U. unfold w64. f_equal.
  apply (dn_U_len E (re_buf e1 + Z.of_nat p - 1) (re_buf e1) (re_used e1) (Z.of_nat p)); try lia.
  - rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. reflexivity.
  - exact E34.
  - exact E35. }
assert (SRC : src_ok SEGS W1 (ms_regs ms) (ms_mem ms) x n).
{ intros y Hy. split.
  - rewrite KEEP1 by lia.
    replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
    rewrite (dn_garr8_aview W1 m1 (re_buf e1) _ _ Hbuf8); [discriminate|].
    rewrite dn_bzs_len, length_app. lia.
  - rewrite Usp1. lia. }
assert (AMR : amem_range x n).
{ rewrite RQC in HBia. unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
  unfold x, n. clear - HBia HBceil Husedr Hpl HUL HAC. lia. }
assert (RA : range_addressable (aview SEGS (w_H W1) (ms_mem ms)) SHADOW_OFF x n)
  by (apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1)); [exact HARm | exact Hbin | lia | rewrite RQC; lia]).
assert (HV : 0 < n -> shadow_hull_vis (aview SEGS (w_H W1) (ms_mem ms)) x n)
  by (intros Hn; apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1)); [exact HARm | exact Hbin | lia | rewrite RQC; lia | exact Hn]).
pose proof (consts_view_of_rom_view SEGS 0x10350 0x10370 W1 (ms_mem ms) HCROM ROM1) as CV.
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_memchr)
    (fun _ => False)
    (fun regs' (_ : word -> option byte) => exists k, first_byte SEGS W1 (ms_mem ms) x n 0 k /\
       getr regs' 10 = (if k <? n then w64 (x + k) else w64 0))
    W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5188)) HG eq_refl HJ).
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
    { exact (AMEMCHR ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ x 0 n HPRE G10 Q11 G12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        SRC AMR RA HV CV). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Hres) & Hfr2 & Hpres2).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 ([] : list nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (SHOK2 : sh_ok SEGS Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
paj_run_tok RUN HS HJ2 SHOK2 dn_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFrB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hg into GRB end.
(* the memory at the branch: the call's scratch aside, the cut's *)
assert (KEEPB : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem msB) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy Hs. rewrite (dn_frame_nil _ _ _ _ _ HFrB ltac:(reflexivity) y Hy).
  rewrite (Hfr2 y Hy (fun H => H) ltac:(clear - Hs; lia)). exact (KEEP1 y Hy). }
assert (PRESB : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msB) y).
{ intros y Hp. apply (apresent_grows _ _ _ _ GRB). apply Hpres2. exact (apresent_grows _ _ _ y GR1 Hp). }
assert (HSTK : alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 HDS HES HDF; lia).
(* memchr's result: a0 = s->buf + p + kk when a NUL is found at kk < n, else 0 *)
destruct Hfb as (Hk0 & Hkb & Hkz).
set (a0v := if kk <? n then x + kk else 0).
assert (HA0 : ew Ea 40 = Z_to_bv 64 a0v) by (rewrite <- R10b, Hres; unfold a0v; destruct (kk <? n); reflexivity).
assert (Ra0 : 0 <= a0v < 2 ^ 64)
  by (unfold a0v; destruct (kk <? n); clear - Hxn Hk0 HBceil HAC Husedr HUlen HB4096; lia).
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) (ms_mem ms) (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite KEEP1 by (clear - Hj HUL Husedr HBceil HAC HB4096; lia).
  rewrite (dn_garr8_aview W1 m1 (re_buf e1) _ j Hbuf8)
    by (rewrite dn_bzs_len, length_app; clear - Hj HUL HUlen Hjunk Husedr; lia).
  rewrite dn_bzs_app, app_nth1 by (rewrite dn_bzs_len; clear - Hj HUL HUlen; lia). rewrite HUW. reflexivity. }
psrr_branch_tok RUN BR HS SHOK2 dn_Bspan.
- (* a NUL at s->buf + p + kk: the next line is [p, p + kk) *)
  rewrite branch_ne_U, (U_atom Ea 40 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk < n).
  { destruct (Z.ltb_spec kk n) as [Hl | Hl]; [exact Hl|]. exfalso. unfold a0v in Hc.
    rewrite ?(proj2 (Z.ltb_ge kk n) Hl) in Hc. cbv beta iota in Hc. discriminate Hc. }
  assert (Ha0 : a0v = x + kk) by (unfold a0v; rewrite (proj2 (Z.ltb_lt kk n) Hkk); reflexivity).
  paj_run_to_tok RUNTO HS HJ2 SHOK2 dn_Bspan A_dr_line. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hs. rewrite (dn_frame_nil _ _ _ _ _ HFrF ltac:(reflexivity) y Hy). exact (KEEPB y Hy Hs). }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ y GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy. split; [apply KEEPF; clear - Hy HSTK HAC HES HDF; lia|].
    unfold arm. apply writable_kept. exact (PRESF y). }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdll (p + Z.to_nat kk)%nat W1). unfold DLL.
  exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (dn_dregs_kept cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hregs);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity] | apply (RK _ 9%nat P9); [lia | reflexivity]
      | apply (RK _ 8%nat P8); [lia | reflexivity] | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF ].
    rewrite P27, (OLDa 33%nat ltac:(lia)), E33, R27. unfold w64. rewrite unsigned_lit_small by (clear - HSAlo HSAhi HGceil HAC HG4096; lia).
    reflexivity. }
  split; [rewrite P23, HA0, Ha0; unfold w64, x; f_equal; clear - Hk0; lia|].
  split.
  { rewrite P24, (OLDa 23%nat ltac:(lia)), (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. unfold w64.
    rewrite unsigned_lit_small by (clear - HB4096 HBceil HAC Hpl HUL Husedr; lia). f_equal. lia. }
  split; [exact HBD|].
  split; [unfold n in Hkk; clear - Hkk Hk0 HUL; lia|].
  split.
  { pose proof (Hkz Hkk) as Hz.
    replace (x + kk) with (re_buf e1 + Z.of_nat (p + Z.to_nat kk)) in Hz by (unfold x; clear - Hk0; lia).
    rewrite BV in Hz by (unfold n in Hkk; clear - Hkk Hk0 HUL; lia). injection Hz as Hz.
    rewrite (nth_error_nth' (dW s1) 0) by (unfold n in Hkk; clear - Hkk Hk0 HUL; lia). rewrite Hz. reflexivity. }
  split.
  { intros i Hi. destruct (Hkb (Z.of_nat i - Z.of_nat p) ltac:(clear - Hi Hk0; lia)) as (b & Hb & Hb0).
    replace (x + (Z.of_nat i - Z.of_nat p)) with (re_buf e1 + Z.of_nat i) in Hb by (unfold x; clear; lia).
    rewrite BV in Hb by (unfold n in Hkk; clear - Hi Hkk Hk0 HUL; lia). injection Hb as <-.
    rewrite (nth_error_nth' (dW s1) 0) by (unfold n in Hkk; clear - Hi Hkk Hk0 HUL; lia).
    intros Hn0. injection Hn0 as Hn0. exact (Hb0 Hn0). }
  split; [|exact Hdlfut].
  exact (dn_dlc_kept cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF
    (proj1 HSTK) (proj2 HSTK) HSAlo HSAhi (proj1 (proj2 (proj2 (proj2 HBrest))))
    HDLC HJ2 KEEPF PRESF).
- (* no NUL in [p, |W|): the loop's exit *)
  rewrite branch_ne_U, (U_atom Ea 40 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk = n).
  { destruct (Z.ltb_spec kk n) as [Hl | Hl]; [|clear - Hl Hk0; lia]. exfalso. unfold a0v in Hc.
    rewrite ?(proj2 (Z.ltb_lt kk n) Hl) in Hc. cbv beta iota in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    clear - Hc Hxn Hk0. lia. }
  paj_run_to_tok RUNTO HS HJ2 SHOK2 dn_Bspan A_dr_rest. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hs. rewrite (dn_frame_nil _ _ _ _ _ HFrF ltac:(reflexivity) y Hy). exact (KEEPB y Hy Hs). }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ y GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy. split; [apply KEEPF; clear - Hy HSTK HAC HES HDF; lia|].
    unfold arm. apply writable_kept. exact (PRESF y). }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdlr W1). unfold DLR.
  exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (dn_dregs_kept cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hregs);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity] | apply (RK _ 9%nat P9); [lia | reflexivity]
      | apply (RK _ 8%nat P8); [lia | reflexivity] | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF ].
    rewrite P27, (OLDa 33%nat ltac:(lia)), E33, R27. unfold w64. rewrite unsigned_lit_small by (clear - HSAlo HSAhi HGceil HAC HG4096; lia).
    reflexivity. }
  split.
  { rewrite P24, (OLDa 23%nat ltac:(lia)), (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. unfold w64.
    rewrite unsigned_lit_small by (clear - HB4096 HBceil HAC Hpl HUL Husedr; lia). f_equal. lia. }
  split.
  { rewrite P25.
    transitivity (sv_denot Ea (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 23 0)
      (SLit 18446744073709551615)) (SLit (-1))) (SOff 34 0)) (SOff 35 0))).
    { cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
    rewrite denot_lit_U. unfold w64. f_equal.
    rewrite (dn_U_len Ea (re_buf e1 + Z.of_nat p - 1) (re_buf e1) (re_used e1) (Z.of_nat p));
      [clear - HUL Hpl; lia | | | | clear - HB4096 HBceil HAC Hpl HUL Husedr Hcpos; lia | clear - HB4096 HBceil HAC Hcpos; lia
      | clear - Husedr HBceil HAC HB4096 HUL Hcpos; lia | lia | clear - Hpl HUL Husedr HBceil HAC HB4096 Hcpos; lia].
    - rewrite (OLDa 23%nat ltac:(lia)), (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. reflexivity.
    - rewrite (OLDa 34%nat ltac:(lia)). exact E34.
    - rewrite (OLDa 35%nat ltac:(lia)). exact E35. }
  split; [rewrite P26, (OLDa 34%nat ltac:(lia)), E34; reflexivity|].
  split; [exact HBD|].
  split.
  { intros i Hi. destruct (Nat.lt_ge_cases i (length (dW s1))) as [Hil | Hil].
    - destruct (Hkb (Z.of_nat i - Z.of_nat p) ltac:(unfold n in Hkk; clear - Hi Hil Hkk HUL; lia)) as (b & Hb & Hb0).
      replace (x + (Z.of_nat i - Z.of_nat p)) with (re_buf e1 + Z.of_nat i) in Hb by (unfold x; clear; lia).
      rewrite BV in Hb by exact Hil. injection Hb as <-.
      rewrite (nth_error_nth' (dW s1) 0) by exact Hil.
      intros Hn0. injection Hn0 as Hn0. exact (Hb0 Hn0).
    - rewrite (proj2 (nth_error_None (dW s1) i) Hil). discriminate. }
  split; [|exact Hdlfut].
  exact (dn_dlc_kept cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF
    (proj1 HSTK) (proj2 HSTK) HSAlo HSAhi (proj1 (proj2 (proj2 (proj2 HBrest))))
    HDLC HJ2 KEEPF PRESF).
Qed.

End c.

(* ---- THE GENERIC WALK (route (b), step 3): NEXT over any allocator relation ARx with its laws, at the room
   texts (the room record RP, the entry's budget kr).  The Section is W_drain_cx_x.v's Section c - its variables
   B PST ARx MT RP MMAX RG in that order, each hypothesis that file's text - with the three allocator rules in their
   caller-context forms (W_journal_x.v Section hc, one context table per allocator entry; this segment calls no
   allocator, so no call-site fact HCTX_* is stated), and after LAWS the generic-relation facts the walk reads:
     HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: the table's and the buffer's shadow facts are
     W_journal_x.v's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x).
   The AR walk above (Section c) is unchanged.  Its Definitions are cited; its lemmas are restated here with an _x
   suffix (each over ARx where it reads the relation), so no lemma's Section generalization is relied on. ---- *)
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
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
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
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
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

(* ---- What the call leaves.  memchr writes nothing outside its scratch [sp - ESTACK, sp); every byte the cut's
   representations read lies below alloc_ceiling (a live block, the image) or in drain's frame [sp, sp + 336),
   so the cut's memory core moves to the memory after the call (W_drain_pro.v's pro_*_low, without key slack). *)
Ltac dn_in := repeat (first [left; reflexivity | right]).

Lemma dn_blk_low_x : forall ly S Hp (W : world SEGS) mem md q n a,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a < q + req_size n -> dn_low a.
Proof.
intros ly S Hp W mem md q n a HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
unfold dn_low. lia.
Qed.

Lemma dn_img_low_x : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= 0x5fb000 -> dn_low a.
Proof.
intros a lo hi H1 H2 H3 H4. pose proof (@ASAN_CEIL_range rc) as (HC & _). unfold ASAN_CEIL in HC. unfold dn_low. lia.
Qed.

Lemma dn_key_ptrs_len_x : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dn_recs_len_x : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dn_aentry_fp_low_x : forall ly S Hp (W : world SEGS) mem md e,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S Hp W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & Hle & Hbuf & _ & Hhp & _ & _ & Hks).
assert (KH : In r (gfp (re_hp e) (bzs (key_ptrs (re_keys e))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e)) -> dn_low a).
{ intros Hr'. destruct Hr' as [<- | Hr'].
  - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite dn_bzs_len, dn_key_ptrs_len_x in Ha.
    destruct Hhp as [(Hz & Hke) | (Hz & Hin & Hk1 & Hk2 & _)].
    + rewrite Hke in Ha. cbn [length] in Ha. lia.
    + apply (dn_blk_low_x ly S Hp W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
      pose proof (dn_req_ge (re_kh e)). unfold re_nheld in Hk1. lia.
  - apply in_map_iff in Hr' as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite dn_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    apply (dn_blk_low_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
    pose proof (dn_req_ge (Z.of_nat (length (key_text k)) + 1)). lia. }
unfold aentry_fp in Hr. destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; cbn [app] in Hr.
- exact (KH Hr).
- destruct Hr as [<- | Hr]; [|exact (KH Hr)].
  unfold gfp in Ha. cbn [fst snd] in Ha. rewrite dn_bzs_len, length_app in Ha.
  destruct Hbuf as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
  apply (dn_blk_low_x ly S Hp W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
  pose proof (dn_req_ge (re_cap e)). lia.
Qed.

Lemma dn_alist_fp_low_x : forall ly S Hp (W : world SEGS) mem md LA l lines lo hi,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S Hp W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dn_img_low_x a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite dn_bzs_len, length_app, dn_recs_len_x in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (dn_blk_low_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (dn_req_ge (AREC * hl_cap l)) as Hrq.
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite dn_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (dn_blk_low_x ly S Hp W mem md (fst q) (Z.of_nat (length (snd q)) + 1) a HAR Hin); [lia|].
    pose proof (dn_req_ge (Z.of_nat (length (snd q)) + 1)). lia.
Qed.

Lemma dn_asrc_fp_low_x : forall ly S Hp (W : world SEGS) mem md HA h,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S Hp W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dn_img_low_x a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite dn_bzs_len in Ha.
  apply (dn_blk_low_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (dn_req_ge APARTIAL). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (dn_alist_fp_low_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (dn_alist_fp_low_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
    * refine (dn_alist_fp_low_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
Qed.

Lemma dn_aout_fp_low_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> dn_low a.
Proof.
intros ly S Hp W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (@ASAN_CEIL_range rc) as (HC & _). unfold ASAN_CEIL in HC.
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> dn_low a).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI). unfold dn_low, kLowMemEnd in *. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (dn_img_low_x a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; dn_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; dn_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; dn_in | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (dn_img_low_x a (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; dn_in | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (dn_img_low_x a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; dn_in | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; dn_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (dn_blk_low_x ly S Hp W mem md out cap a HAR Hin); [lia|].
  pose proof (dn_req_ge cap). lia.
Qed.

(* W_drain_gs.v gs_aentry_okx_kept (W_rep.v aentry_ok_kept for aentry_okx), ported *)
Lemma dn_aentry_okx_kept_x : forall ly S W mem ly' S' W' mem' e,
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

(* drain's frame: every slot lies in [sp, sp + 336) *)
Lemma dn_frame_kept_x : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
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

(* the line loop's registers and frame slots, moved to a state that keeps the nine registers and the frame *)
Lemma dn_dregs_kept_x : forall cx regs regs' (W : world SEGS) m m',
dregs_line RG cx regs W m ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 22 = getr regs 22 -> getr regs' 27 = getr regs 27 -> getr regs' 18 = getr regs 18 ->
getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 -> getr regs' 21 = getr regs 21 ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W m' a) ->
dregs_line RG cx regs' W m'.
Proof.
intros cx regs regs' W m m' HR E2 E3 E4 E22 E27 E18 E9 E8 E21 KF.
destruct HR as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
unfold dregs_line. unfold spZ in *. rewrite E2, E3, E4, E22, E27, E18, E9, E8, E21.
do 9 (split; [assumption|]).
split; [exact (dn_frame_kept_x cx W m W m' KF HFR)|].
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
apply V; [lia | lia | assumption].
Qed.

(* a run whose symbolic state has no region writes nothing *)
Lemma dn_frame_nil_x : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> rs = [] ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hn a Ha. apply (aview_kept_out E rs H m m' HF a Ha). subst rs. intros (r & Hin & _). destruct Hin.
Qed.

Lemma dn_entry_x : forall (W : world SEGS) regs1 m1 sp SA BUF USED,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 27 = w64 (SA + 24) -> 4096 <= SA -> SA + 32 <= DN_HI -> SA + 32 <= sp ->
0 <= BUF < 2 ^ 64 -> 0 <= USED < 2 ^ 64 ->
val_mem SEGS (arm W m1) (sp + 200) 8 (SA + 16) ->
val_mem SEGS (arm W m1) (sp + 216) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W m1) (sp + 224) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W m1) (SA + 16) 8 BUF ->
val_mem SEGS (arm W m1) (SA + 24) 8 USED ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dn_extra SA BUF USED))) ss_dn
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_next)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 sp SA BUF USED Hsp Hlo Hhi Hal R27 HSA1 HSA2 HSA3 HBUF HUSED M200 M216 M224 MBUF MUSED.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (dn_extra SA BUF USED))).
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 BUF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 USED) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (Usa : bv_unsigned (ew E 33) = SA) by (rewrite E33; apply unsigned_lit_small; unfold DN_HI in *; lia).
unfold DN_HI in HSA2. unfold DRAIN_FRAME in Hhi.
unfold ss_dn. apply pa_entry_st_ok_full.
- unfold dn_regs. apply regs_ok_pin;
    [ | intros X; discriminate X
    | rewrite (den_atom E 33%nat SA 24 E33) by lia; exact R27 ].
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dn_regions, dn_frame, dn_ent.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?Usa.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 200 8 (SOff 33 16) (SA + 16));
      [rewrite (den_atom E 33%nat SA 16 E33) by lia; reflexivity | cbn; lia | cbn; lia | exact M200].
    * apply (chunk_ok_val SEGS E _ sp 216 8 _ (shadow_addr (SA + 16)));
      [apply dn_den; rewrite (dn_U_shadow E 33 SA 16 E33 E32) by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply dn_shadow_range; lia
      | cbn; lia | exact M216].
    * apply (chunk_ok_val SEGS E _ sp 224 8 _ (shadow_addr (SA + 24)));
      [apply dn_den; rewrite (dn_U_shadow E 33 SA 24 E33 E32) by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply dn_shadow_range; lia
      | cbn; lia | exact M224].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ SA 16 8 (SOff 34 0) BUF);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact MBUF].
    * apply (chunk_ok_val SEGS E _ SA 24 8 (SOff 35 0) USED);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact MUSED].
- apply pairwise_disjoint_of_extents. unfold dn_regions, dn_frame, dn_ent, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usa.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [dn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usa, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, DN_HI. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* ---- Route R: the R twins of the cut lemmas and of the segment, at a world relation R that contains wle (the
   journal and the step relation at R). The strict dr_next_x after this Section is dr_next_xR at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PI).

(* the cut's memory core, moved across a step that keeps every byte outside [sp - ESTACK, sp) *)
Lemma dn_dmem_kept_xR : forall cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 m2 md2,
alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE -> (dxj cx < 4)%nat ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m2 md2 k1 e1 h1 s out1 ev1 sent LB1.
Proof.
intros cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 m2 md2 Hst Htop HG1 HG2 Hj HM HJ2 KV KP.
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HGSB as (Hg1 & Hg2 & _).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
  abyte_kept W1 m1 W1 m2 a).
{ intros a Ha Hn. split; [exact (KV a Ha Hn)|]. unfold arm. apply writable_kept. exact (KP a). }
assert (KL : forall a, dn_low a -> abyte_kept W1 m1 W1 m2 a)
  by (intros a Ha; unfold dn_low in Ha; apply KB; [clear - Ha Hst Htop HES HDF; lia | clear - Ha Hst HES HDF; lia]).
pose proof (@ASAN_CEIL_range rc) as (HC & _). unfold ASAN_CEIL in HC.
assert (KF : forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W1 m1 W1 m2 a)
  by (intros a Ha; apply KB; [clear - Ha Hst Htop HES HDF HC; lia | clear - Ha; lia]).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (SAL : forall a, dxSA cx <= a < dxSA cx + AENT -> dn_low a).
{ intros a Ha. apply (dn_blk_low_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE a HAR HTB); [lia|].
  pose proof (dn_req_ge ATABLE). lia. }
assert (INB : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1))
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _).
unfold DMEM_xR.
split; [exact HJ2|].
split.
{ intros a Ha.
  assert (Hai : 65536 <= a < 6270976)
    by (destruct Ha as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite KV; [exact (Hrom a Ha) | clear - Hai; lia | clear - Hai Hst HC HES HDF; lia]. }
split; [intros a Ha1 Ha2 Ha3 Hq; apply KP; exact (Hpres a Ha1 Ha2 Ha3 Hq)|].
split; [exact Hframes|].
split; [exact (dn_frame_kept_x cx W1 m1 W1 m2 KF HFR)|].
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx. apply KL. apply SAL.
  rewrite (dn_entry_len e1 Hpad1 Hpad2) in Hx. unfold AENT. lia. }
split; [apply (akept_awr W1 m1); [intros x Hx; apply KL; apply SAL; exact Hx | exact Hawr]|].
split.
{ apply (dn_aentry_okx_kept_x ly1 S1 W1 m1); [exact HOKX | | intros b Hb; apply INB; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KL. exact (dn_aentry_fp_low_x ly1 S1 Hp1 W1 m1 md1 e1 HAR HOKX r Hr x Hx). }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1); [exact Hsrc | |
    intros b Hb; apply INB; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KL.
  refine (dn_asrc_fp_low_x ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) h1 HAR Hsrc _ _ r Hr x Hx);
  unfold dHA, ASRC in *; clear - Hj; nia. }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o.
  split; [|split; [|exact Ho]]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx; apply KL;
  apply (dn_img_low_x x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; cbn in Hx; clear - Hx Hi Hg1 Hg2; nia. }
split.
{ intros x Hx Hn. destruct (Hgsk x Hx Hn) as [A1 A2].
  assert (Hxl : dn_low x) by (apply (dn_img_low_x x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia).
  destruct (KL x Hxl) as [B1 B2]. split; [rewrite B1; exact A1 | intros Hw; apply B2; apply A2; exact Hw]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1); [exact Hout | |
    intros b Hb; apply INB; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KL. exact (dn_aout_fp_low_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ HAR Hout r Hr x Hx). }
split; [exact Hlivout | exact Hperm].
Qed.

Lemma dn_dlc_kept_xR : forall cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2,
alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE -> (dxj cx < 4)%nat ->
DLC_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DLC_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p ly1 S1 Hp1 W1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 Hst Htop HG1 HG2 Hj HD HJ2 KV KP.
unfold DLC_xR, LCORE_xR in *. destruct HD as (HM & HR). split; [|exact HR].
exact (dn_dmem_kept_xR cx Hp _ _ Hp1 _ _ _ _ _ _ _ _ _ _ _ m2 md2 Hst Htop HG1 HG2 Hj HM HJ2 KV KP).
Qed.

(* ---- NEXT at R: DLN 0x836f4 -> memchr #2 (0x8372c) -> DLL (a NUL at q) / DLR (none). ---- *)
Theorem dr_next_xR : dr_next_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_next_stmt_xR. intros cx Hpe kr s1 D p W1 c1 HB HDLN Hdll Hdlr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
unfold DLN_xR in HDLN.
destruct HDLN as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl
  & Hcfg & Hregs & H23 & Hbound & Hp0 & HDLC & Hdlfut).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsaved).
pose proof HDLC as HDLC'. unfold DLC_xR, LCORE_xR in HDLC'.
destruct HDLC' as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & HBx10 & Htbl & HSAlo & HSAhi & HBrest).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *.
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
assert (HUW : bzs (re_U e1) = dW s1).
{ destruct HLINK as (_ & HU & _). unfold dvirt in HU. cbn [drain_b_c.ds_u] in HU. exact HU. }
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, dn_bzs_len; lia).
assert (Hcapb : re_cap e1 <= 16384) by (clear - Hcapr; destruct Hcapr as [Hq | [Hq | Hq]]; lia).
pose proof Hbound as HBD. destruct Hbound as (Hpl & Hpz). clear Hpz Heof Hskip Hcapr Hheld.
assert (Hcap0 : re_cap e1 <> 0) by (intros Hc; rewrite Hc in Husedr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & HBpres & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil.
(* the entry's two cells *)
pose proof (dn_entry_buf W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MBUF.
pose proof (dn_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MUSED.
(* the symbolic state *)
pose proof (dn_entry_x W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_used e1) Hsp
  ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity) R27 ltac:(lia) ltac:(unfold DN_HI; lia)
  ltac:(lia) ltac:(lia) ltac:(lia) M200 F216 F224 MBUF MUSED) as HS.
remember (Eimg (Ereg regs1 (dn_extra (dxSA cx) (re_buf e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (dn_extra (dxSA cx) (re_buf e1) (re_used e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_used e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (SHOK : sh_ok SEGS Bx DN_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E Bx 33 (dxSA cx + 16) 16 (dxSA cx) 16 32).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE); [exact HAR | exact HTB | lia | unfold ATABLE; rewrite RQT; lia].
  - unfold Bx. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). reflexivity.
  - apply (U_atom E 33 (dxSA cx) E33). lia.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    rewrite Z.min_l, Z.max_r in Hx by lia. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_next)) with (Z_to_bv 64 (BASE + A_dr_next)).
paj_run_tok_xR RUNR HS HJ SHOK dn_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
(* the run before the call wrote nothing *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_dn dn_regions In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi dn_frame dn_ent] in Hr; lia. }
assert (HARm : ARx ly1 S1 Hp1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR_xR; exact HJ).
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros x Hx. rewrite KEEP1; [exact (Hrom x Hx)|].
  destruct Hx as (sg & Hsg & _ & Hr). pose proof (pa_img_range x ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
(* memchr (s->buf + p, 0, s->used - p) *)
set (x := re_buf e1 + Z.of_nat p). set (n := re_used e1 - Z.of_nat p).
assert (Hxn : 4096 <= x /\ 0 <= n /\ x + n = re_buf e1 + re_used e1) by (unfold x, n; lia).
assert (Usp1 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (G10 : getr (ms_regs ms) 10 = w64 x).
{ rewrite Q10, (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. unfold w64.
  rewrite unsigned_lit_small by lia. f_equal. unfold x. lia. }
assert (G12 : getr (ms_regs ms) 12 = w64 n).
{ rewrite Q12.
  transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 23 0)
    (SLit 18446744073709551615)) (SLit (-1))) (SOff 34 0)) (SOff 35 0))).
  { cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
  rewrite denot_lit_U. unfold w64. f_equal.
  apply (dn_U_len E (re_buf e1 + Z.of_nat p - 1) (re_buf e1) (re_used e1) (Z.of_nat p)); try lia.
  - rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. reflexivity.
  - exact E34.
  - exact E35. }
assert (SRC : src_ok SEGS W1 (ms_regs ms) (ms_mem ms) x n).
{ intros y Hy. split.
  - rewrite KEEP1 by lia.
    replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
    rewrite (dn_garr8_aview W1 m1 (re_buf e1) _ _ Hbuf8); [discriminate|].
    rewrite dn_bzs_len, length_app. lia.
  - rewrite Usp1. lia. }
assert (AMR : amem_range x n).
{ rewrite RQC in HBia. unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
  unfold x, n. clear - HBia HBceil Husedr Hpl HUL HAC. lia. }
assert (RA : range_addressable (aview SEGS (w_H W1) (ms_mem ms)) SHADOW_OFF x n)
  by (apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1)); [exact HARm | exact Hbin | lia | rewrite RQC; lia]).
assert (HV : 0 < n -> shadow_hull_vis (aview SEGS (w_H W1) (ms_mem ms)) x n)
  by (intros Hn; apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1)); [exact HARm | exact Hbin | lia | rewrite RQC; lia | exact Hn]).
pose proof (consts_view_of_rom_view SEGS 0x10350 0x10370 W1 (ms_mem ms) HCROM ROM1) as CV.
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_memchr)
    (fun _ => False)
    (fun regs' (_ : word -> option byte) => exists k, first_byte SEGS W1 (ms_mem ms) x n 0 k /\
       getr regs' 10 = (if k <? n then w64 (x + k) else w64 0))
    W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5188)) HG eq_refl HJ).
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
    { exact (AMEMCHR ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) _ x 0 n HPRE G10 Q11 G12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        SRC AMR RA HV CV). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Hres) & Hfr2 & Hpres2).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 ([] : list nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (SHOK2 : sh_ok SEGS Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
paj_run_tok_xR RUNR HS HJ2 SHOK2 dn_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFrB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hg into GRB end.
(* the memory at the branch: the call's scratch aside, the cut's *)
assert (KEEPB : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem msB) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy Hs. rewrite (dn_frame_nil_x _ _ _ _ _ HFrB ltac:(reflexivity) y Hy).
  rewrite (Hfr2 y Hy (fun H => H) ltac:(clear - Hs; lia)). exact (KEEP1 y Hy). }
assert (PRESB : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msB) y).
{ intros y Hp. apply (apresent_grows _ _ _ _ GRB). apply Hpres2. exact (apresent_grows _ _ _ y GR1 Hp). }
assert (HSTK : alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 HDS HES HDF; lia).
(* memchr's result: a0 = s->buf + p + kk when a NUL is found at kk < n, else 0 *)
destruct Hfb as (Hk0 & Hkb & Hkz).
set (a0v := if kk <? n then x + kk else 0).
assert (HA0 : ew Ea 40 = Z_to_bv 64 a0v) by (rewrite <- R10b, Hres; unfold a0v; destruct (kk <? n); reflexivity).
assert (Ra0 : 0 <= a0v < 2 ^ 64)
  by (unfold a0v; destruct (kk <? n); clear - Hxn Hk0 HBceil HAC Husedr HUlen HB4096; lia).
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) (ms_mem ms) (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite KEEP1 by (clear - Hj HUL Husedr HBceil HAC HB4096; lia).
  rewrite (dn_garr8_aview W1 m1 (re_buf e1) _ j Hbuf8)
    by (rewrite dn_bzs_len, length_app; clear - Hj HUL HUlen Hjunk Husedr; lia).
  rewrite dn_bzs_app, app_nth1 by (rewrite dn_bzs_len; clear - Hj HUL HUlen; lia). rewrite HUW. reflexivity. }
psrr_branch_tok RUNR BRR HS SHOK2 dn_Bspan.
- (* a NUL at s->buf + p + kk: the next line is [p, p + kk) *)
  rewrite branch_ne_U, (U_atom Ea 40 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk < n).
  { destruct (Z.ltb_spec kk n) as [Hl | Hl]; [exact Hl|]. exfalso. unfold a0v in Hc.
    rewrite ?(proj2 (Z.ltb_ge kk n) Hl) in Hc. cbv beta iota in Hc. discriminate Hc. }
  assert (Ha0 : a0v = x + kk) by (unfold a0v; rewrite (proj2 (Z.ltb_lt kk n) Hkk); reflexivity).
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 dn_Bspan A_dr_line. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hs. rewrite (dn_frame_nil_x _ _ _ _ _ HFrF ltac:(reflexivity) y Hy). exact (KEEPB y Hy Hs). }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ y GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy. split; [apply KEEPF; clear - Hy HSTK HAC HES HDF; lia|].
    unfold arm. apply writable_kept. exact (PRESF y). }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdll (p + Z.to_nat kk)%nat W1). unfold DLL_xR.
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF), mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (dn_dregs_kept_x cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hregs);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity] | apply (RK _ 9%nat P9); [lia | reflexivity]
      | apply (RK _ 8%nat P8); [lia | reflexivity] | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF ].
    rewrite P27, (OLDa 33%nat ltac:(lia)), E33, R27. unfold w64. rewrite unsigned_lit_small by (clear - HSAlo HSAhi HGceil HAC HG4096; lia).
    reflexivity. }
  split; [rewrite P23, HA0, Ha0; unfold w64, x; f_equal; clear - Hk0; lia|].
  split.
  { rewrite P24, (OLDa 23%nat ltac:(lia)), (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. unfold w64.
    rewrite unsigned_lit_small by (clear - HB4096 HBceil HAC Hpl HUL Husedr; lia). f_equal. lia. }
  split; [exact HBD|].
  split; [unfold n in Hkk; clear - Hkk Hk0 HUL; lia|].
  split.
  { pose proof (Hkz Hkk) as Hz.
    replace (x + kk) with (re_buf e1 + Z.of_nat (p + Z.to_nat kk)) in Hz by (unfold x; clear - Hk0; lia).
    rewrite BV in Hz by (unfold n in Hkk; clear - Hkk Hk0 HUL; lia). injection Hz as Hz.
    rewrite (nth_error_nth' (dW s1) 0) by (unfold n in Hkk; clear - Hkk Hk0 HUL; lia). rewrite Hz. reflexivity. }
  split.
  { intros i Hi. destruct (Hkb (Z.of_nat i - Z.of_nat p) ltac:(clear - Hi Hk0; lia)) as (b & Hb & Hb0).
    replace (x + (Z.of_nat i - Z.of_nat p)) with (re_buf e1 + Z.of_nat i) in Hb by (unfold x; clear; lia).
    rewrite BV in Hb by (unfold n in Hkk; clear - Hi Hkk Hk0 HUL; lia). injection Hb as <-.
    rewrite (nth_error_nth' (dW s1) 0) by (unfold n in Hkk; clear - Hi Hkk Hk0 HUL; lia).
    intros Hn0. injection Hn0 as Hn0. exact (Hb0 Hn0). }
  split; [|exact Hdlfut].
  exact (dn_dlc_kept_xR cx Hpe kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF
    (proj1 HSTK) (proj2 HSTK) HSAlo HSAhi (proj1 (proj2 (proj2 (proj2 HBrest))))
    HDLC HJ2 KEEPF PRESF).
- (* no NUL in [p, |W|): the loop's exit *)
  rewrite branch_ne_U, (U_atom Ea 40 a0v HA0 Ra0), (U_lit Ea 0) in Hc by lia.
  assert (Hkk : kk = n).
  { destruct (Z.ltb_spec kk n) as [Hl | Hl]; [|clear - Hl Hk0; lia]. exfalso. unfold a0v in Hc.
    rewrite ?(proj2 (Z.ltb_lt kk n) Hl) in Hc. cbv beta iota in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    clear - Hc Hxn Hk0. lia. }
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 dn_Bspan A_dr_rest. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (KEEPF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hs. rewrite (dn_frame_nil_x _ _ _ _ _ HFrF ltac:(reflexivity) y Hy). exact (KEEPB y Hy Hs). }
  assert (PRESF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hp; exact (apresent_grows _ _ _ y GRF (PRESB y Hp))).
  assert (KFF : forall y, dsp0 cx - DRAIN_FRAME <= y < dsp0 cx -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy. split; [apply KEEPF; clear - Hy HSTK HAC HES HDF; lia|].
    unfold arm. apply writable_kept. exact (PRESF y). }
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> (k < 32)%nat ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; assumption. }
  match goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
  apply (Hdlr W1). unfold DLR_xR.
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF), mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply (dn_dregs_kept_x cx regs1 (ms_regs msF) W1 m1 (ms_mem msF) Hregs);
      [ apply (RK _ 2%nat P2); [lia | reflexivity] | apply (RK _ 3%nat P3); [lia | reflexivity]
      | apply (RK _ 4%nat P4); [lia | reflexivity] | apply (RK _ 22%nat P22); [lia | reflexivity]
      | | apply (RK _ 18%nat P18); [lia | reflexivity] | apply (RK _ 9%nat P9); [lia | reflexivity]
      | apply (RK _ 8%nat P8); [lia | reflexivity] | apply (RK _ 21%nat P21); [lia | reflexivity] | exact KFF ].
    rewrite P27, (OLDa 33%nat ltac:(lia)), E33, R27. unfold w64. rewrite unsigned_lit_small by (clear - HSAlo HSAhi HGceil HAC HG4096; lia).
    reflexivity. }
  split.
  { rewrite P24, (OLDa 23%nat ltac:(lia)), (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. unfold w64.
    rewrite unsigned_lit_small by (clear - HB4096 HBceil HAC Hpl HUL Husedr; lia). f_equal. lia. }
  split.
  { rewrite P25.
    transitivity (sv_denot Ea (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 23 0)
      (SLit 18446744073709551615)) (SLit (-1))) (SOff 34 0)) (SOff 35 0))).
    { cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
    rewrite denot_lit_U. unfold w64. f_equal.
    rewrite (dn_U_len Ea (re_buf e1 + Z.of_nat p - 1) (re_buf e1) (re_used e1) (Z.of_nat p));
      [clear - HUL Hpl; lia | | | | clear - HB4096 HBceil HAC Hpl HUL Husedr Hcpos; lia | clear - HB4096 HBceil HAC Hcpos; lia
      | clear - Husedr HBceil HAC HB4096 HUL Hcpos; lia | lia | clear - Hpl HUL Husedr HBceil HAC HB4096 Hcpos; lia].
    - rewrite (OLDa 23%nat ltac:(lia)), (EREG 23%nat 23%bv ltac:(lia) eq_refl), H23. reflexivity.
    - rewrite (OLDa 34%nat ltac:(lia)). exact E34.
    - rewrite (OLDa 35%nat ltac:(lia)). exact E35. }
  split; [rewrite P26, (OLDa 34%nat ltac:(lia)), E34; reflexivity|].
  split; [exact HBD|].
  split.
  { intros i Hi. destruct (Nat.lt_ge_cases i (length (dW s1))) as [Hil | Hil].
    - destruct (Hkb (Z.of_nat i - Z.of_nat p) ltac:(unfold n in Hkk; clear - Hi Hil Hkk HUL; lia)) as (b & Hb & Hb0).
      replace (x + (Z.of_nat i - Z.of_nat p)) with (re_buf e1 + Z.of_nat i) in Hb by (unfold x; clear; lia).
      rewrite BV in Hb by exact Hil. injection Hb as <-.
      rewrite (nth_error_nth' (dW s1) 0) by exact Hil.
      intros Hn0. injection Hn0 as Hn0. exact (Hb0 Hn0).
    - rewrite (proj2 (nth_error_None (dW s1) i) Hil). discriminate. }
  split; [|exact Hdlfut].
  exact (dn_dlc_kept_xR cx Hpe kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem msF) mdF
    (proj1 HSTK) (proj2 HSTK) HSAlo HSAhi (proj1 (proj2 (proj2 (proj2 HBrest))))
    HDLC HJ2 KEEPF PRESF).
Qed.

End wR.

(* ---- NEXT: DLN 0x836f4 -> memchr #2 (0x8372c) -> DLL (a NUL at q) / DLR (none): dr_next_xR at R := wle
   (dr_next_stmt_xR at wle is dr_next_stmt_x by conversion). ---- *)
Theorem dr_next_x : dr_next_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dr_next_xR (@wle SEGS) (wle_trans SEGS) (fun _ _ H => H)). Qed.

End cx.
End b.
End a.
