(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require X0m8.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cy X1cp X1cj X1dd X1cg X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1d2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0j3 X0hi
X0hn X0hh X0hb X0il X0gp X0h2 X0j4 X0hf X0fy X0jc.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X19m X183 X188 X182 X17w X196 X17a X17n X19n X180 X16j X19t.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19t.
Import ListNotations.
Open Scope Z_scope.

Definition cpw (c i : Z) : word := Z_to_bv 64 ((i * ClassSize c) / 16).

Definition icells_rep (L : layoutA) (m : mem) : Prop :=
rw_cells bsegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)]
/\ ro_cells bsegs m 0x1976dd [C1 (Z_to_bv 8 0)] /\ ro_cells bsegs m 0x1976e4 [C1 (Z_to_bv 8 1)]
/\ ro_cells bsegs m 0xfc110 [C8 (Z_to_bv 64 0x1032b8)] /\ ro_cells bsegs m 0xfc140 [C8 (Z_to_bv 64 0xfe038)]
/\ ro_cells bsegs m 0xfe038 [C8 (Z_to_bv 64 0xf16f4)] /\ ro_cells bsegs m 0x1032d5 [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m 0x1067bc [C4 (Z_to_bv 64 30)] /\ ro_cells bsegs m 0x19760a [C1 (Z_to_bv 8 1)]

/\ ro_cells bsegs m 0xfce58 [C8 (Z_to_bv 64 0x658cd8)] /\ ro_cells bsegs m 0xfce58 [C8 (Z_to_bv 64 0x658cd8)]

/\ ro_cells bsegs m 0xfcc80 [C8 (Z_to_bv 64 0x106799)] /\ ro_cells bsegs m 0x106799 [C1 (Z_to_bv 8 1)]
/\ ro_cells bsegs m 0xfe040 [C8 (Z_to_bv 64 0xf1af8)] /\ ro_cells bsegs m 0xfdef8 [C8 (Z_to_bv 64 0xf15f8)]
/\ ro_cells bsegs m 0xfdfe8 [C8 (Z_to_bv 64 0xf1f80)] /\ ro_cells bsegs m 0xfded0 [C8 (Z_to_bv 64 0xf1d44)]
/\ ro_cells bsegs m 0x1976e3 [C1 (Z_to_bv 8 1)]

/\ rw_cells bsegs m 0x103278 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells bsegs m 0x103280 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
/\ rw_cells bsegs m 0x187d22 [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0x19760a [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m 0xfc110 [C8 (Z_to_bv 64 0x1032b8)] /\ rw_cells bsegs m (0x1032b8 + 44) [C4 (Z_to_bv 64 4096)]
/\ rw_cells bsegs m (0x1032b8 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells bsegs m (0x1032b8 + 85) [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m (0x638c98 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0xfcd70 [C8 (Z_to_bv 64 16)]
/\ rw_cells bsegs m 0x197580 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x10531c [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
/\ stk bsegs m (l_T L + 2768) (l_T L + 3168)

/\ rw_cells bsegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]

/\ rw_cells bsegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
/\ rw_cells bsegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]

/\ rw_cells bsegs m 0xfc158 [C8 (Z_to_bv 64 1)] /\ rw_cells bsegs m 0x1976c3 [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m 0x1976dc [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xfce58 [C8 (Z_to_bv 64 0x658cd8)]
/\ rw_cells bsegs m 0x658f58 [C8 (Z_to_bv 64 4096)]

/\ Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro.

Definition consts_rep (L : layoutA) (m : mem) : Prop :=
inst_cells (l_SB L) m /\ mm_gcells m /\ thread_cells (l_TCX L) (l_T L) m /\ m2s_cells m /\ ps_cells m
/\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m /\ client_consts m /\ icells_rep L m.

Definition reg_rep (SB c : Z) (r : regst) (m : mem) : Prop :=
let R := rinfo (RIS_of SB) c in
let auser := ClassSize c * Z.of_nat (length (r_st r)) in
ri_lock m R 0 /\ ri_core m R (Z.of_nat (length (r_fl r))) (r_mfa r) auser (r_muser r)
/\ (exists rand exh pad nal nfr r0 r1 r2 r3, ri_tail m R rand exh pad nal nfr r0 r1 r2 r3)
/\ (exists ws, fl_arr m SB c ws /\ 4 * Z.of_nat (length ws) = r_mfa r /\ firstn (length (r_fl r)) ws = map (cpw c) (r_fl r))
/\ stk bsegs m (rb SB c + auser) (rb SB c + r_muser r)
/\ bytes_at bsegs m (shad (rb SB c + auser)) (farun ((r_muser r - auser) / 8))
/\ stk bsegs m (shad (rb SB c)) (shad (rb SB c + 2 ^ 32)).
Definition prim_rep (Σ : rtsA) (m : mem) : Prop := forall c, 1 <= c <= 31 -> reg_rep (l_SB (lay Σ)) c (pr Σ c) m.

Definition pclass_rep (T c : Z) (init : bool) (l : list Z) (m : mem) : Prop :=
pc_cells m (pc_addr T c) (Z.of_nat (length l)) (if init then MaxCount c else 0) (if init then ClassSize c else 0)
/\ exists chs, u32arr bsegs m (pc_addr T c + 16) chs /\ length chs = 16%nat /\ firstn (length l) chs = map (cpw c) l.
Definition cache_rep (Σ : rtsA) (m : mem) : Prop :=
forall c, 1 <= c <= 31 -> pclass_rep (l_T (lay Σ)) c (ca_init Σ) (ca Σ c) m.

Definition pchunk (SB c : Z) (i : nat) (st : ckst) (m : mem) : Prop :=
let AB := p_abeg SB c i in let S := ClassSize c in
match st with
| CkIdle => stk bsegs m AB (AB + S) /\ pshadow_idle m AB S
| CkBatch => pshadow_idle m AB S
| CkAlloc n => wr_at bsegs m AB S /\ ahdr m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
/\ pshadow_alloc m AB S n
| CkQuar n => wr_at bsegs m AB S /\ qhdr3 m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
/\ pshadow_quar m AB S n
end.

Definition schunk (k : nat) (s : secst) (m : mem) : Prop :=
let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
shdr m mb msz (needed n + rz_size n) (Z.of_nat k) /\ wr_at bsegs m mb msz /\ lch m AB M
/\ (if s_quar s then qhdr3 m M n else ahdr m M n)
/\ stk bsegs m (shad mb) (shad (mb + msz))
/\ bytes_at bsegs m (shad mb) (farun ((4096 + 2048) / 8))
/\ bytes_at bsegs m (shad (AB + 2048)) (if s_quar s then fdrun (ru8 n / 8) else ushadow n)
/\ bytes_at bsegs m (shad (AB + 2048 + ru8 n)) (farun ((msz - 4096 - 2048 - ru8 n) / 8)).
Definition chunk_rep (Σ : rtsA) (m : mem) : Prop :=
(forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk (l_SB (lay Σ)) c i st m)
/\ (forall k s, nth_error (sec Σ) k = Some s -> schunk k s m).

Definition sec_rep (Σ : rtsA) (m : mem) : Prop :=
sec_core m (l_PAB (lay Σ)) (sec_nres Σ) (Z.of_nat (length (sec Σ))) /\ sec_pad m
/\ (exists ws, u64arr bsegs m (l_PAB (lay Σ)) ws /\ Z.of_nat (length ws) = sec_nres Σ
/\ firstn (length (sec Σ)) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ))
/\ sec_page m /\ sec_range m (l_PAB (lay Σ)) /\ sec_junk m /\ name_cells m     .

Definition quar_rep (Σ : rtsA) (m : mem) : Prop :=
qcache_rep m (qcacheT (l_T (lay Σ))) (ql Σ) /\ qcache_rep m i_q_global (qg Σ)
/\ rw_cells bsegs m i_q_cmutex [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)].

Definition dep_rep (L : layoutA) (d : depot) (m : mem) : Prop := depot_rep d (DEP_BK (hash_of (d_hs d) 1)) (l_DNB L) (l_SSB L) m.

Definition fs_cls_rep (FSB c : Z) (f : fsst) (m : mem) : Prop :=
fs_hint FSB c m (fss_hint f) /\ fs_flags FSB c m (fss_flags f) /\ fs_free_frames FSB c m (fss_flags f).

Definition fs_busy (L : layoutA) (frs : list (Z * nat)) (m : mem) : Prop :=
Forall (fun fk => exists p, fst fk = frame_addr (l_FSB L) (Z.of_nat (snd fk)) p
/\ wr_at bsegs m (fst fk) (fs_size (snd fk)) /\ wr_at bsegs m (shad (fst fk)) (fs_size (snd fk) / 8)
/\ rw_cells bsegs m (fst fk + fs_size (snd fk) - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB L) (Z.of_nat (snd fk)) + p))]) frs.
Definition fs_rep (Σ : rtsA) (m : mem) : Prop :=
let L := lay Σ in let FSB := l_FSB L in
fs_const FSB m /\ fs_cls_rep FSB 0 (fs0 Σ) m /\ fs_cls_rep FSB 2 (fs2 Σ) m /\ (fs_cls_rep FSB 4 (fs4 Σ) m /\ fs_cls_rep FSB 5 (fsc Σ 5%nat) m /\ fs_cls_rep FSB 8 (fsc Σ 8%nat) m)
/\ rw_cells bsegs m tpA [C8 (Z_to_bv 64 FSB)]
/\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
/\ (exists tb te, ttls_cells (l_T L) m tb te)
/\ fs_busy L (frames Σ) m.

Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

Definition CS_W : list (Z * Z) :=
[(0x100750, 0x102458); (0x628110, 0x638110); (0x638110, 0x638c40); (0x638c48, 0x638c90); (0x638cb0, 0x638cb8); (0x638cc8, 0x658f58); (0x658f60, 0x65a040); (0x65a048, 0x65a578)].

Definition CS_ACC : list (Z * Z) :=
[(0x100750, 0x100ab0); (0x1023f0, 0x102458); (0x628110, 0x638110); (0x638110, 0x638c40); (0x638c48, 0x638c90); (0x638cb0, 0x638cb8); (0x638cc8, 0x658f58); (0x658f60, 0x65a040); (0x65a048, 0x65a578);

(0x232a0, 0x232b8); (0x232e0, 0x232e6); (0x23360, 0x23387); (0x233c0, 0x233f0); (0x23420, 0x23453); (0x23480, 0x2349e);
(0x234c0, 0x234eb); (0x23520, 0x23545); (0x23580, 0x23592); (0x235c0, 0x235cd); (0x23600, 0x23620); (0x23640, 0x23650);
(0x23760, 0x23770); (0x237a0, 0x237a9); (0x237c0, 0x237d7); (0x23800, 0x23827); (0x23860, 0x23872); (0x238c0, 0x238cb);
(0x23a80, 0x23a99); (0x23ac0, 0x23ae5); (0x23b20, 0x23b3c); (0x23b60, 0x23b80); (0x23ba0, 0x23ba4); (0x23bc0, 0x23bc8);
(0x23be0, 0x23c0c); (0x23c40, 0x23c68); (0x23ca0, 0x23cc0); (0x23ce0, 0x23d13); (0x23d40, 0x23d7e); (0x23da0, 0x23dc7);
(0x23e00, 0x23e2e); (0x23e60, 0x23e70); (0x23e80, 0x23eab); (0x23ee0, 0x23ef2); (0x23f20, 0x23f4c); (0x23f80, 0x242a0);
(0x24380, 0x2450c); (0x24580, 0x2465c); (0x24680, 0x246d8); (0x24720, 0x2475c); (0x24780, 0x247bc); (0x247e0, 0x24834);
(0x24880, 0x24b00); (0x24ba0, 0x24ce0); (0x24d20, 0x24e60); (0x24ea0, 0x24fe0); (0x25020, 0x25160); (0x251c0, 0x253c0);
(0x25440, 0x25640); (0x256e0, 0x25760); (0x257a0, 0x25840); (0x25880, 0x259c0); (0x25a20, 0x25e20); (0x25f40, 0x26140);
(0x261e0, 0x26320); (0x26380, 0x26880); (0x269e0, 0x26c60); (0x26d20, 0x26d39); (0x26d60, 0x26d80); (0x26da0, 0x26dbf);
(0x26de0, 0x26df0); (0x26fc0, 0x26fd9); (0x27000, 0x27100); (0x27140, 0x271c0); (0x271e0, 0x27220); (0x27240, 0x27273);
(0x272a0, 0x272b0); (0x272c0, 0x272d2); (0x27320, 0x27460); (0x274c0, 0x278c0); (0xf8380, 0xf8450); (0xf8480, 0xf84e0);
(0xf8500, 0xf8558); (0xf8580, 0xf85d8); (0xf8600, 0xf8658); (0xf8680, 0xf86d8); (0xf8700, 0xf8758); (0xf8780, 0xf87d8);
(0xf8800, 0xf8858); (0xf8880, 0xf88d8); (0xf8900, 0xf8910); (0xf8920, 0xf8938); (0xf8960, 0xf8970); (0xf8980, 0xf8998);
(0xf89c0, 0xf89d0); (0xf89e0, 0xf89f8); (0xf8a20, 0xf8a30); (0xf8a40, 0xf8a58); (0xf8a80, 0xf8a98); (0xf8ac0, 0xf8ad8);
(0xf8b00, 0xf8b60); (0xf8b80, 0xf8be0); (0xf8c00, 0xf8c18); (0xf8c40, 0xf8c98); (0xf8cc0, 0xf8d18); (0xf8d40, 0xf8d98);
(0xf8dc0, 0xf8e18); (0xf8e40, 0xf8f18); (0xf8f40, 0xf8f58); (0xf8f80, 0xf8f98); (0xf8fc0, 0xf9098);

(0x10f54, 0x10f5e); (0x1529e, 0x152a2); (0x165c0, 0x16640); (0x1ac77, 0x1ac98); (0x1f32d, 0x1f342); (0x1f342, 0x1f359); (0x219c0, 0x21a40); (0x22ad2, 0x22ad9); (0x23708, 0x23718); (0xfc010, 0xfc018); (0x628100, 0x628110)].

Definition static_acc (m : mem) : Prop := Forall (fun r => acc bsegs m (fst r) (snd r - fst r)) CS_ACC.

Definition pois_wf (L : layoutA) (P : list (Z * Z)) : Prop :=
Forall (fun e => fst e mod 32 = 0 /\ 0 <= snd e /\ l_ACEIL L + 64 <= pz_lo e /\ pz_hi e <= USTACK_TOP - 16) P
/\ ForallOrdPairs (fun e1 e2 => pz_hi e1 <= pz_lo e2) P.

Definition stack_shadow_rep (L : layoutA) (P : list (Z * Z)) (m : mem) : Prop :=
l_ACEIL L mod 8 = 0
/\ (forall a, l_ACEIL L <= a < 2 ^ 47 -> ~ in_pois P a -> bytes_at bsegs m (shad a) [z8])
/\ Forall (fun e => acc bsegs m (fst e) (snd e)) P
/\ pois_wf L P.

Lemma stack_shadow_rep_nil : forall L (m : mem), l_ACEIL L mod 8 = 0 -> 0 <= l_ACEIL L ->
bytes_at bsegs m (shad (l_ACEIL L)) (zrun ((2 ^ 47 - l_ACEIL L) / 8)) -> stack_shadow_rep L [] m.
Proof.
intros L m M8 H0 B. split; [exact M8|]. split; [|split; [constructor | split; constructor]].
intros a Ha _. unfold zrun in B.
apply Z.mod_divide in M8; [|lia]. destruct M8 as [q Hq].
assert (Hqa : q <= a / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hs : shad a = shad (l_ACEIL L) + Z.of_nat (Z.to_nat (a / 8 - q))).
{ rewrite Z2Nat.id by lia. unfold shad. rewrite Hq, Z.div_mul by lia. lia. }
rewrite Hs. apply (bytes_at_nth1 bsegs m _ _ _ _ B). apply nth_error_repeat. apply Nat2Z.inj_lt.
rewrite !Z2Nat.id; [| apply Z.div_pos; lia | lia].
rewrite Hq. replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia.
assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Definition shadow_rep (L : layoutA) (P : list (Z * Z)) (m : mem) : Prop :=
stack_shadow_rep L P m
/\ stk bsegs m (shad (l_ACEIL L)) (shad (2 ^ 47))
/\ stk bsegs m (pg_dn (shad 0x10000)) (shad SEGTOP_A)
/\ static_acc m.

Definition shreg (z : Z) : Prop := (K_LOW_SHADOW_lo <= z < K_LOW_SHADOW_hi) \/ (K_HIGH_SHADOW_lo <= z < K_HIGH_SHADOW_hi).

Definition vis_rep (L : layoutA) (A : list (Z * Z)) (m : mem) : Prop :=
forall a : word, shreg (bv_unsigned a) -> page_allowedb A (page_base a) = true ->
bv_unsigned a < shad (pg_dn (l_ACEIL L)) ->
(forall e, In e (l_maps0 L) -> ~ (shad (bv_unsigned (fst e)) <= bv_unsigned a < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
m a <> None.

Lemma vis_rep_wmono : forall {L} A (m m' : mem), vis_rep L A m -> wmono bsegs m m' -> vis_rep L A m'.
Proof.
intros L A m m' H WM a Hs Hp Hlo Hx. pose proof (H a Hs Hp Hlo Hx) as Ha.
assert (NS : find_segment bsegs (bv_unsigned a) 1 = None).
{ unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments.
cbn [find_segment].
unfold AsanUbsan.AsanUbsan_segment_000, AsanUbsan.AsanUbsan_segment_001,
AsanUbsan.AsanUbsan_segment_002, AsanUbsan.AsanUbsan_segment_003.
cbn [seg_base seg_size]. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs.
destruct Hs as [Hs|Hs];
repeat match goal with |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]; cbn [andb] end; reflexivity. }
assert (W0 : wview bsegs m a <> None) by (unfold wview; destruct (m a); [discriminate | congruence]).
pose proof (WM a W0) as W1. unfold wview in W1. destruct (m' a) eqn:E; [discriminate|]. rewrite NS in W1. exact W1.
Qed.

Definition ART_A (Σ : rtsA) (m : mem) : Prop :=
rt_wf Σ /\ consts_rep (lay Σ) m /\ prim_rep Σ m /\ cache_rep Σ m /\ chunk_rep Σ m /\ sec_rep Σ m /\ quar_rep Σ m
/\ dep_rep (lay Σ) (dep Σ) m /\ fs_rep Σ m /\ ia_rep Σ m /\ shadow_rep (lay Σ) (rtA_pois Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

Definition lazy_in_maps_A (mo : Model) : Prop :=
forall iv, In iv (m_vm_lazy mo) -> 0 < bv_unsigned (snd iv) ->
exists e, In e (vm_maps (m_vmmaps mo)) /\ bv_unsigned (fst e) <= bv_unsigned (fst iv)
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e) + bv_unsigned (snd e).
Definition iv_apart (p q : word * word) : Prop :=
bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Definition confined0 (Σ : rtsA) (mo : Model) : Prop :=
forall z, X0m8.covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) z = true -> X0m8.covered (l_maps0 (lay Σ)) z = true.

Definition shadow_lazy (mo : Model) : Prop :=
forall a : word, shreg (bv_unsigned a) ->
page_in_ranges (page_base a) (m_vm_lazy mo) = true /\ X0m8.covered (vm_noaccess (m_vmmaps mo)) (bv_unsigned a) = false.

Definition maps_zbound (mo : Model) : Prop :=
Z.of_nat (length (vm_maps (m_vmmaps mo))) <= Z.of_nat (length (List.filter vpos (vm_maps (m_vmmaps mo)))) + 1.
Definition artm_sys (Σ : rtsA) (mo : Model) : Prop :=
X0m8.model_ivs_wf mo /\ lazy_in_maps_A mo /\ ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo))
/\ bv_unsigned (vm_init_sp (m_vmmaps mo)) = l_sp0 (lay Σ) /\ confined0 Σ mo /\ shadow_lazy mo /\ maps_zbound mo

/\ X1d2.noaccess_pos mo.

Definition ARTM_A (Σ : rtsA) (mo : Model) : Prop :=
Permutation (List.filter vpos (vm_maps (m_vmmaps mo))) (rt_maps Σ) /\ vm_reserved (m_vmmaps mo) = segments_reserved bsegs
/\ vm_limit (m_vmmaps mo) = VMLIMIT /\ eager_used mo <= E0_MAX + rt_eager Σ /\ artm_sys Σ mo.

Definition RTA : rt_sig := mkRTS rtsA ART_A ARTM_A rtA_live rtA_frames rtA_allow rtA_sp0 rtA_credit rtA_pois.

Lemma filter_map_remove : forall (l : list (word * word)) (a : word), List.filter vpos (map_remove l a) = map_remove (List.filter vpos l) a.
Proof.
intros l a. unfold map_remove. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter].
destruct (negb (bv_eqb (fst e) a)) eqn:Eb; destruct (vpos e) eqn:Ev; cbn [List.filter]; rewrite ?Eb, ?Ev, IH; reflexivity.
Qed.

Lemma perm_filter' : forall {T : Type} (f : T -> bool) (l l' : list T), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
intros T f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [List.filter].
- constructor.
- destruct (f x); [constructor; exact IH | exact IH].
- destruct (f x); destruct (f y); cbn [List.filter]; [apply perm_swap | apply Permutation_refl | apply Permutation_refl | apply Permutation_refl].
- exact (Permutation_trans IH1 IH2).
Qed.

Lemma perm_map_remove : forall (l l' : list (word * word)) (a : word), Permutation l l' -> Permutation (map_remove l a) (map_remove l' a).
Proof. intros l l' a H. unfold map_remove. apply perm_filter'. exact H. Qed.

Lemma filter_cons_pos : forall (e : word * word) (l : list (word * word)), 0 < bv_unsigned (snd e) -> List.filter vpos (e :: l) = e :: List.filter vpos l.
Proof. intros e l H. cbn [List.filter]. unfold vpos. rewrite (proj2 (Z.ltb_lt 0 _) H). reflexivity. Qed.

Lemma filter_vpos_pos : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) (List.filter vpos l).
Proof.
intros l. apply Forall_forall. intros e He. apply List.filter_In in He as [_ He]. unfold vpos in He. apply Z.ltb_lt in He. exact He.
Qed.

Lemma filter_vpos_id : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) l -> List.filter vpos l = l.
Proof.
intros l H. induction H as [|e l He _ IH]; [reflexivity|]. rewrite (filter_cons_pos e l He), IH. reflexivity.
Qed.

Lemma covered_filter_vpos : forall (l : list (word * word)) (z : Z), X0m8.covered (List.filter vpos l) z = X0m8.covered l z.
Proof.
intros l z. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter]. destruct (vpos e) eqn:Ev.
- unfold X0m8.covered in *. cbn [existsb]. rewrite IH. reflexivity.
- unfold X0m8.covered in *. cbn [existsb]. rewrite IH. unfold vpos in Ev. apply Z.ltb_ge in Ev.
pose proof (bv_unsigned_in_range _ (snd e)) as Hr. unfold X0m8.in_iv, X0m8.in_rng, X0m8.B, X0m8.S.
replace (bv_unsigned (snd e)) with 0 by (unfold bv_modulus in Hr; lia).
destruct (bv_unsigned (fst e) <=? z) eqn:E1; destruct (z <? bv_unsigned (fst e) + 0) eqn:E2; cbn [andb orb]; try reflexivity.
apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma vis_premise_filter : forall (l : list (word * word)) (x : Z),
(forall e, In e (List.filter vpos l) -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
forall e, In e l -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e))).
Proof.
intros l x H e He. destruct (vpos e) eqn:Ev.
- exact (H e (proj2 (List.filter_In _ _ _) (conj He Ev))).
- unfold vpos in Ev. apply Z.ltb_ge in Ev. pose proof (bv_unsigned_in_range _ (snd e)) as Hr.
replace (bv_unsigned (snd e)) with 0 by (unfold bv_modulus in Hr; lia). rewrite Z.add_0_r. lia.
Qed.

Section Proj.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
Lemma ART_wf : rt_wf Σ. Proof. exact (proj1 HA). Qed.
Lemma ART_consts : consts_rep (lay Σ) m. Proof. exact (proj1 (proj2 HA)). Qed.
Lemma ART_prim : prim_rep Σ m. Proof. exact (proj1 (proj2 (proj2 HA))). Qed.
Lemma ART_cache : cache_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 HA)))). Qed.
Lemma ART_chunk : chunk_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HA))))). Qed.
Lemma ART_sec : sec_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))). Qed.
Lemma ART_quar : quar_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))). Qed.
Lemma ART_dep : dep_rep (lay Σ) (dep Σ) m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))). Qed.
Lemma ART_fs : fs_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))). Qed.
Lemma ART_ia : ia_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))))). Qed.
Lemma ART_shadow : shadow_rep (lay Σ) (rtA_pois Σ) m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
Lemma ART_vis : vis_rep (lay Σ) (rtA_allow Σ) m. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
End Proj.

Lemma ART_intro : forall Σ m, rt_wf Σ -> consts_rep (lay Σ) m -> prim_rep Σ m -> cache_rep Σ m -> chunk_rep Σ m ->
sec_rep Σ m -> quar_rep Σ m -> dep_rep (lay Σ) (dep Σ) m -> fs_rep Σ m -> ia_rep Σ m -> shadow_rep (lay Σ) (rtA_pois Σ) m ->
vis_rep (lay Σ) (rtA_allow Σ) m -> ART_A Σ m.
Proof. intros. unfold ART_A. repeat (split; [assumption|]). assumption. Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition cpw (c i : Z) : word := Z_to_bv 64 ((i * ClassSize c) / 16).

Definition icells_rep (L : layoutA) (m : mem) : Prop :=
rw_cells asegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)]
/\ ro_cells asegs m 0x18ee9d [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x18eea4 [C1 (Z_to_bv 8 1)]
/\ ro_cells asegs m 0xf3890 [C8 (Z_to_bv 64 0xfaa78)] /\ ro_cells asegs m 0xf38c0 [C8 (Z_to_bv 64 0xf57b8)]
/\ ro_cells asegs m 0xf57b8 [C8 (Z_to_bv 64 0xe8e80)] /\ ro_cells asegs m 0xfaa95 [C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m 0xfdf7c [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x18edca [C1 (Z_to_bv 8 1)]

/\ ro_cells asegs m 0xf45d8 [C8 (Z_to_bv 64 0x650498)] /\ ro_cells asegs m 0xf45d8 [C8 (Z_to_bv 64 0x650498)]

/\ ro_cells asegs m 0xf4400 [C8 (Z_to_bv 64 0xfdf59)] /\ ro_cells asegs m 0xfdf59 [C1 (Z_to_bv 8 1)]
/\ ro_cells asegs m 0xf57c0 [C8 (Z_to_bv 64 0xe9284)] /\ ro_cells asegs m 0xf5678 [C8 (Z_to_bv 64 0xe8d84)]
/\ ro_cells asegs m 0xf5768 [C8 (Z_to_bv 64 0xe970c)] /\ ro_cells asegs m 0xf5650 [C8 (Z_to_bv 64 0xe94d0)]
/\ ro_cells asegs m 0x18eea3 [C1 (Z_to_bv 8 1)]

/\ rw_cells asegs m 0xfaa38 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0xfaa40 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
/\ rw_cells asegs m 0x17f4e2 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x18edca [C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m 0xf3890 [C8 (Z_to_bv 64 0xfaa78)] /\ rw_cells asegs m (0xfaa78 + 44) [C4 (Z_to_bv 64 4096)]
/\ rw_cells asegs m (0xfaa78 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0xfaa78 + 85) [C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m (0x630458 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xf44f0 [C8 (Z_to_bv 64 16)]
/\ rw_cells asegs m 0x18ed40 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xfcadc [C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
/\ stk asegs m (l_T L + 2768) (l_T L + 3168)

/\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]

/\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
/\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
/\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]

/\ rw_cells asegs m 0xf38d8 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x18ee83 [C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m 0x18ee9c [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xf45d8 [C8 (Z_to_bv 64 0x650498)]
/\ rw_cells asegs m 0x650718 [C8 (Z_to_bv 64 4096)]

/\ Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro.

Definition consts_rep (L : layoutA) (m : mem) : Prop :=
inst_cells (l_SB L) m /\ mm_gcells m /\ thread_cells (l_TCX L) (l_T L) m /\ m2s_cells m /\ ps_cells m
/\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m /\ client_consts m /\ icells_rep L m.

Definition reg_rep (SB c : Z) (r : regst) (m : mem) : Prop :=
let R := rinfo (RIS_of SB) c in
let auser := ClassSize c * Z.of_nat (length (r_st r)) in
ri_lock m R 0 /\ ri_core m R (Z.of_nat (length (r_fl r))) (r_mfa r) auser (r_muser r)
/\ (exists rand exh pad nal nfr r0 r1 r2 r3, ri_tail m R rand exh pad nal nfr r0 r1 r2 r3)
/\ (exists ws, fl_arr m SB c ws /\ 4 * Z.of_nat (length ws) = r_mfa r /\ firstn (length (r_fl r)) ws = map (cpw c) (r_fl r))
/\ stk asegs m (rb SB c + auser) (rb SB c + r_muser r)
/\ bytes_at asegs m (shad (rb SB c + auser)) (farun ((r_muser r - auser) / 8))
/\ stk asegs m (shad (rb SB c)) (shad (rb SB c + 2 ^ 32)).
Definition prim_rep (Σ : rtsA) (m : mem) : Prop := forall c, 1 <= c <= 31 -> reg_rep (l_SB (lay Σ)) c (pr Σ c) m.

Definition pclass_rep (T c : Z) (init : bool) (l : list Z) (m : mem) : Prop :=
pc_cells m (pc_addr T c) (Z.of_nat (length l)) (if init then MaxCount c else 0) (if init then ClassSize c else 0)
/\ exists chs, u32arr asegs m (pc_addr T c + 16) chs /\ length chs = 16%nat /\ firstn (length l) chs = map (cpw c) l.
Definition cache_rep (Σ : rtsA) (m : mem) : Prop :=
forall c, 1 <= c <= 31 -> pclass_rep (l_T (lay Σ)) c (ca_init Σ) (ca Σ c) m.

Definition pchunk (SB c : Z) (i : nat) (st : ckst) (m : mem) : Prop :=
let AB := p_abeg SB c i in let S := ClassSize c in
match st with
| CkIdle => stk asegs m AB (AB + S) /\ pshadow_idle m AB S
| CkBatch => pshadow_idle m AB S
| CkAlloc n => wr_at asegs m AB S /\ ahdr m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
/\ pshadow_alloc m AB S n
| CkQuar n => wr_at asegs m AB S /\ qhdr3 m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
/\ pshadow_quar m AB S n
end.

Definition schunk (k : nat) (s : secst) (m : mem) : Prop :=
let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
shdr m mb msz (needed n + rz_size n) (Z.of_nat k) /\ wr_at asegs m mb msz /\ lch m AB M
/\ (if s_quar s then qhdr3 m M n else ahdr m M n)
/\ stk asegs m (shad mb) (shad (mb + msz))
/\ bytes_at asegs m (shad mb) (farun ((4096 + 2048) / 8))
/\ bytes_at asegs m (shad (AB + 2048)) (if s_quar s then fdrun (ru8 n / 8) else ushadow n)
/\ bytes_at asegs m (shad (AB + 2048 + ru8 n)) (farun ((msz - 4096 - 2048 - ru8 n) / 8)).
Definition chunk_rep (Σ : rtsA) (m : mem) : Prop :=
(forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk (l_SB (lay Σ)) c i st m)
/\ (forall k s, nth_error (sec Σ) k = Some s -> schunk k s m).

Definition sec_rep (Σ : rtsA) (m : mem) : Prop :=
sec_core m (l_PAB (lay Σ)) (sec_nres Σ) (Z.of_nat (length (sec Σ))) /\ sec_pad m
/\ (exists ws, u64arr asegs m (l_PAB (lay Σ)) ws /\ Z.of_nat (length ws) = sec_nres Σ
/\ firstn (length (sec Σ)) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ))
/\ sec_page m /\ sec_range m (l_PAB (lay Σ)) /\ sec_junk m /\ name_cells m     .

Definition quar_rep (Σ : rtsA) (m : mem) : Prop :=
qcache_rep m (qcacheT (l_T (lay Σ))) (ql Σ) /\ qcache_rep m i_q_global (qg Σ)
/\ rw_cells asegs m i_q_cmutex [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)].

Definition dep_rep (L : layoutA) (d : depot) (m : mem) : Prop := depot_rep d (DEP_BK (hash_of (d_hs d) 1)) (l_DNB L) (l_SSB L) m.

Definition fs_cls_rep (FSB c : Z) (f : fsst) (m : mem) : Prop :=
fs_hint FSB c m (fss_hint f) /\ fs_flags FSB c m (fss_flags f) /\ fs_free_frames FSB c m (fss_flags f).

Definition fs_busy (L : layoutA) (frs : list (Z * nat)) (m : mem) : Prop :=
Forall (fun fk => exists p, fst fk = frame_addr (l_FSB L) (Z.of_nat (snd fk)) p
/\ wr_at asegs m (fst fk) (fs_size (snd fk)) /\ wr_at asegs m (shad (fst fk)) (fs_size (snd fk) / 8)
/\ rw_cells asegs m (fst fk + fs_size (snd fk) - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB L) (Z.of_nat (snd fk)) + p))]) frs.
Definition fs_rep (Σ : rtsA) (m : mem) : Prop :=
let L := lay Σ in let FSB := l_FSB L in
fs_const FSB m /\ fs_cls_rep FSB 0 (fs0 Σ) m /\ fs_cls_rep FSB 2 (fs2 Σ) m /\ (fs_cls_rep FSB 4 (fs4 Σ) m /\ fs_cls_rep FSB 5 (fsc Σ 5%nat) m /\ fs_cls_rep FSB 8 (fsc Σ 8%nat) m)
/\ rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)]
/\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
/\ (exists tb te, ttls_cells (l_T L) m tb te)
/\ fs_busy L (frames Σ) m.

Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

Definition CS_W : list (Z * Z) :=
[(0xf7ed0, 0xf9c18); (0x61f8d0, 0x62f8d0); (0x62f8d0, 0x630400); (0x630408, 0x630450); (0x630470, 0x630478); (0x630488, 0x650718); (0x650720, 0x651800); (0x651808, 0x651d38)].

Definition CS_ACC : list (Z * Z) :=
[(0xf7ed0, 0xf8230); (0xf9bb0, 0xf9c18); (0x61f8d0, 0x62f8d0); (0x62f8d0, 0x630400); (0x630408, 0x630450); (0x630470, 0x630478); (0x630488, 0x650718); (0x650720, 0x651800); (0x651808, 0x651d38);

(0x23260, 0x23278); (0x232a0, 0x232a6); (0x23320, 0x23347); (0x23380, 0x233b0); (0x233e0, 0x23413); (0x23440, 0x2345e);
(0x23480, 0x234ab); (0x234e0, 0x23505); (0x23540, 0x23552); (0x23580, 0x2358d); (0x235c0, 0x235e0); (0x23600, 0x23610);
(0x23720, 0x23730); (0x23760, 0x23769); (0x23780, 0x23797); (0x237c0, 0x237e7); (0x23820, 0x23832); (0x23880, 0x2388b);
(0x23a40, 0x23a59); (0x23a80, 0x23aa5); (0x23ae0, 0x23aea); (0x23b00, 0x23b1c); (0x23b40, 0x23b60); (0x23b80, 0x23b84);
(0x23ba0, 0x23ba8); (0x23bc0, 0x23bec); (0x23c20, 0x23c48); (0x23c80, 0x23ca0); (0x23cc0, 0x23cf3); (0x23d20, 0x23d5e);
(0x23d80, 0x23da7); (0x23de0, 0x23e0e); (0x23e40, 0x23e50); (0x23e60, 0x23e8b); (0x23ec0, 0x23ed2); (0x23f20, 0x23f4c);
(0x23f80, 0x242a0); (0x24380, 0x2450c); (0x24580, 0x2465c); (0x24680, 0x246d8); (0x24720, 0x2475c); (0x24780, 0x247bc);
(0x247e0, 0x24834); (0x24880, 0x24b00); (0x24ba0, 0x24ce0); (0x24d20, 0x24e60); (0x24ea0, 0x24fe0); (0x25020, 0x25160);
(0x251c0, 0x253c0); (0x25440, 0x25640); (0x256e0, 0x25760); (0x257a0, 0x25840); (0x25880, 0x259c0); (0x25a20, 0x25e20);
(0x25f40, 0x26140); (0x261e0, 0x26320); (0x26380, 0x26880); (0x269e0, 0x26c60); (0x26d20, 0x26d39); (0x26d60, 0x26d80);
(0x26da0, 0x26dbf); (0x26de0, 0x26df0); (0x26fc0, 0x26fd9); (0x27000, 0x27100); (0x27140, 0x271c0); (0x271e0, 0x27220);
(0x27240, 0x27273); (0x272a0, 0x272b0); (0x272c0, 0x272d2); (0x27320, 0x27460); (0x274c0, 0x278c0); (0xefb00, 0xefbd0);
(0xefc00, 0xefc60); (0xefc80, 0xefcd8); (0xefd00, 0xefd58); (0xefd80, 0xefdd8); (0xefe00, 0xefe58); (0xefe80, 0xefed8);
(0xeff00, 0xeff58); (0xeff80, 0xeffd8); (0xf0000, 0xf0058); (0xf0080, 0xf0090); (0xf00a0, 0xf00b8); (0xf00e0, 0xf00f0);
(0xf0100, 0xf0118); (0xf0140, 0xf0150); (0xf0160, 0xf0178); (0xf01a0, 0xf01b0); (0xf01c0, 0xf01d8); (0xf0200, 0xf0218);
(0xf0240, 0xf0258); (0xf0280, 0xf02e0); (0xf0300, 0xf0360); (0xf0380, 0xf0398); (0xf03c0, 0xf0418); (0xf0440, 0xf0498);
(0xf04c0, 0xf0518); (0xf0540, 0xf0598); (0xf05c0, 0xf0698); (0xf06c0, 0xf06d8); (0xf0700, 0xf0718); (0xf0740, 0xf0818);

(0x10f3c, 0x10f46); (0x151ae, 0x151b2); (0x164c0, 0x16540); (0x1ab8e, 0x1abaf); (0x1f2f3, 0x1f308); (0x1f308, 0x1f31f); (0x21980, 0x21a00); (0x22a98, 0x22a9f); (0x236c8, 0x236d8); (0xf3790, 0xf3798); (0x61f8c0, 0x61f8d0)].

Definition static_acc (m : mem) : Prop := Forall (fun r => acc asegs m (fst r) (snd r - fst r)) CS_ACC.

Definition pois_wf (L : layoutA) (P : list (Z * Z)) : Prop :=
Forall (fun e => fst e mod 32 = 0 /\ 0 <= snd e /\ l_ACEIL L + 64 <= pz_lo e /\ pz_hi e <= USTACK_TOP - 16) P
/\ ForallOrdPairs (fun e1 e2 => pz_hi e1 <= pz_lo e2) P.

Definition stack_shadow_rep (L : layoutA) (P : list (Z * Z)) (m : mem) : Prop :=
l_ACEIL L mod 8 = 0
/\ (forall a, l_ACEIL L <= a < 2 ^ 47 -> ~ in_pois P a -> bytes_at asegs m (shad a) [z8])
/\ Forall (fun e => acc asegs m (fst e) (snd e)) P
/\ pois_wf L P.

Lemma stack_shadow_rep_nil : forall L (m : mem), l_ACEIL L mod 8 = 0 -> 0 <= l_ACEIL L ->
bytes_at asegs m (shad (l_ACEIL L)) (zrun ((2 ^ 47 - l_ACEIL L) / 8)) -> stack_shadow_rep L [] m.
Proof.
intros L m M8 H0 B. split; [exact M8|]. split; [|split; [constructor | split; constructor]].
intros a Ha _. unfold zrun in B.
apply Z.mod_divide in M8; [|lia]. destruct M8 as [q Hq].
assert (Hqa : q <= a / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hs : shad a = shad (l_ACEIL L) + Z.of_nat (Z.to_nat (a / 8 - q))).
{ rewrite Z2Nat.id by lia. unfold shad. rewrite Hq, Z.div_mul by lia. lia. }
rewrite Hs. apply (bytes_at_nth1 asegs m _ _ _ _ B). apply nth_error_repeat. apply Nat2Z.inj_lt.
rewrite !Z2Nat.id; [| apply Z.div_pos; lia | lia].
rewrite Hq. replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia.
assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Definition shadow_rep (L : layoutA) (P : list (Z * Z)) (m : mem) : Prop :=
stack_shadow_rep L P m
/\ stk asegs m (shad (l_ACEIL L)) (shad (2 ^ 47))
/\ stk asegs m (pg_dn (shad 0x10000)) (shad SEGTOP_A)
/\ static_acc m.

Definition shreg (z : Z) : Prop := (K_LOW_SHADOW_lo <= z < K_LOW_SHADOW_hi) \/ (K_HIGH_SHADOW_lo <= z < K_HIGH_SHADOW_hi).

Definition vis_rep (L : layoutA) (A : list (Z * Z)) (m : mem) : Prop :=
forall a : word, shreg (bv_unsigned a) -> page_allowedb A (page_base a) = true ->
bv_unsigned a < shad (pg_dn (l_ACEIL L)) ->
(forall e, In e (l_maps0 L) -> ~ (shad (bv_unsigned (fst e)) <= bv_unsigned a < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
m a <> None.

Lemma vis_rep_wmono : forall {L} A (m m' : mem), vis_rep L A m -> wmono asegs m m' -> vis_rep L A m'.
Proof.
intros L A m m' H WM a Hs Hp Hlo Hx. pose proof (H a Hs Hp Hlo Hx) as Ha.
assert (NS : find_segment asegs (bv_unsigned a) 1 = None).
{ unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments.
cbn [find_segment].
unfold Asan.Asan_segment_000, Asan.Asan_segment_001,
Asan.Asan_segment_002, Asan.Asan_segment_003.
cbn [seg_base seg_size]. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs.
destruct Hs as [Hs|Hs];
repeat match goal with |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]; cbn [andb] end; reflexivity. }
assert (W0 : wview asegs m a <> None) by (unfold wview; destruct (m a); [discriminate | congruence]).
pose proof (WM a W0) as W1. unfold wview in W1. destruct (m' a) eqn:E; [discriminate|]. rewrite NS in W1. exact W1.
Qed.

Definition ART_A (Σ : rtsA) (m : mem) : Prop :=
rt_wf Σ /\ consts_rep (lay Σ) m /\ prim_rep Σ m /\ cache_rep Σ m /\ chunk_rep Σ m /\ sec_rep Σ m /\ quar_rep Σ m
/\ dep_rep (lay Σ) (dep Σ) m /\ fs_rep Σ m /\ ia_rep Σ m /\ shadow_rep (lay Σ) (rtA_pois Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

Definition lazy_in_maps_A (mo : Model) : Prop :=
forall iv, In iv (m_vm_lazy mo) -> 0 < bv_unsigned (snd iv) ->
exists e, In e (vm_maps (m_vmmaps mo)) /\ bv_unsigned (fst e) <= bv_unsigned (fst iv)
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e) + bv_unsigned (snd e).
Definition iv_apart (p q : word * word) : Prop :=
bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Definition confined0 (Σ : rtsA) (mo : Model) : Prop :=
forall z, X0m8.covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) z = true -> X0m8.covered (l_maps0 (lay Σ)) z = true.

Definition shadow_lazy (mo : Model) : Prop :=
forall a : word, shreg (bv_unsigned a) ->
page_in_ranges (page_base a) (m_vm_lazy mo) = true /\ X0m8.covered (vm_noaccess (m_vmmaps mo)) (bv_unsigned a) = false.

Definition maps_zbound (mo : Model) : Prop :=
Z.of_nat (length (vm_maps (m_vmmaps mo))) <= Z.of_nat (length (List.filter vpos (vm_maps (m_vmmaps mo)))) + 1.
Definition artm_sys (Σ : rtsA) (mo : Model) : Prop :=
X0m8.model_ivs_wf mo /\ lazy_in_maps_A mo /\ ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo))
/\ bv_unsigned (vm_init_sp (m_vmmaps mo)) = l_sp0 (lay Σ) /\ confined0 Σ mo /\ shadow_lazy mo /\ maps_zbound mo

/\ X1d2.noaccess_pos mo.

Definition ARTM_A (Σ : rtsA) (mo : Model) : Prop :=
Permutation (List.filter vpos (vm_maps (m_vmmaps mo))) (rt_maps Σ) /\ vm_reserved (m_vmmaps mo) = segments_reserved asegs
/\ vm_limit (m_vmmaps mo) = VMLIMIT /\ eager_used mo <= E0_MAX + rt_eager Σ /\ artm_sys Σ mo.

Definition RTA : rt_sig := mkRTS rtsA ART_A ARTM_A rtA_live rtA_frames rtA_allow rtA_sp0 rtA_credit rtA_pois.

Lemma filter_map_remove : forall (l : list (word * word)) (a : word), List.filter vpos (map_remove l a) = map_remove (List.filter vpos l) a.
Proof.
intros l a. unfold map_remove. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter].
destruct (negb (bv_eqb (fst e) a)) eqn:Eb; destruct (vpos e) eqn:Ev; cbn [List.filter]; rewrite ?Eb, ?Ev, IH; reflexivity.
Qed.

Lemma perm_filter' : forall {T : Type} (f : T -> bool) (l l' : list T), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
intros T f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [List.filter].
- constructor.
- destruct (f x); [constructor; exact IH | exact IH].
- destruct (f x); destruct (f y); cbn [List.filter]; [apply perm_swap | apply Permutation_refl | apply Permutation_refl | apply Permutation_refl].
- exact (Permutation_trans IH1 IH2).
Qed.

Lemma perm_map_remove : forall (l l' : list (word * word)) (a : word), Permutation l l' -> Permutation (map_remove l a) (map_remove l' a).
Proof. intros l l' a H. unfold map_remove. apply perm_filter'. exact H. Qed.

Lemma filter_cons_pos : forall (e : word * word) (l : list (word * word)), 0 < bv_unsigned (snd e) -> List.filter vpos (e :: l) = e :: List.filter vpos l.
Proof. intros e l H. cbn [List.filter]. unfold vpos. rewrite (proj2 (Z.ltb_lt 0 _) H). reflexivity. Qed.

Lemma filter_vpos_pos : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) (List.filter vpos l).
Proof.
intros l. apply Forall_forall. intros e He. apply List.filter_In in He as [_ He]. unfold vpos in He. apply Z.ltb_lt in He. exact He.
Qed.

Lemma filter_vpos_id : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) l -> List.filter vpos l = l.
Proof.
intros l H. induction H as [|e l He _ IH]; [reflexivity|]. rewrite (filter_cons_pos e l He), IH. reflexivity.
Qed.

Lemma covered_filter_vpos : forall (l : list (word * word)) (z : Z), X0m8.covered (List.filter vpos l) z = X0m8.covered l z.
Proof.
intros l z. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter]. destruct (vpos e) eqn:Ev.
- unfold X0m8.covered in *. cbn [existsb]. rewrite IH. reflexivity.
- unfold X0m8.covered in *. cbn [existsb]. rewrite IH. unfold vpos in Ev. apply Z.ltb_ge in Ev.
pose proof (bv_unsigned_in_range _ (snd e)) as Hr. unfold X0m8.in_iv, X0m8.in_rng, X0m8.B, X0m8.S.
replace (bv_unsigned (snd e)) with 0 by (unfold bv_modulus in Hr; lia).
destruct (bv_unsigned (fst e) <=? z) eqn:E1; destruct (z <? bv_unsigned (fst e) + 0) eqn:E2; cbn [andb orb]; try reflexivity.
apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma vis_premise_filter : forall (l : list (word * word)) (x : Z),
(forall e, In e (List.filter vpos l) -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
forall e, In e l -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e))).
Proof.
intros l x H e He. destruct (vpos e) eqn:Ev.
- exact (H e (proj2 (List.filter_In _ _ _) (conj He Ev))).
- unfold vpos in Ev. apply Z.ltb_ge in Ev. pose proof (bv_unsigned_in_range _ (snd e)) as Hr.
replace (bv_unsigned (snd e)) with 0 by (unfold bv_modulus in Hr; lia). rewrite Z.add_0_r. lia.
Qed.

Section Proj.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
Lemma ART_wf : rt_wf Σ. Proof. exact (proj1 HA). Qed.
Lemma ART_consts : consts_rep (lay Σ) m. Proof. exact (proj1 (proj2 HA)). Qed.
Lemma ART_prim : prim_rep Σ m. Proof. exact (proj1 (proj2 (proj2 HA))). Qed.
Lemma ART_cache : cache_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 HA)))). Qed.
Lemma ART_chunk : chunk_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HA))))). Qed.
Lemma ART_sec : sec_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))). Qed.
Lemma ART_quar : quar_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))). Qed.
Lemma ART_dep : dep_rep (lay Σ) (dep Σ) m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))). Qed.
Lemma ART_fs : fs_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))). Qed.
Lemma ART_ia : ia_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))))). Qed.
Lemma ART_shadow : shadow_rep (lay Σ) (rtA_pois Σ) m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
Lemma ART_vis : vis_rep (lay Σ) (rtA_allow Σ) m. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
End Proj.

Lemma ART_intro : forall Σ m, rt_wf Σ -> consts_rep (lay Σ) m -> prim_rep Σ m -> cache_rep Σ m -> chunk_rep Σ m ->
sec_rep Σ m -> quar_rep Σ m -> dep_rep (lay Σ) (dep Σ) m -> fs_rep Σ m -> ia_rep Σ m -> shadow_rep (lay Σ) (rtA_pois Σ) m ->
vis_rep (lay Σ) (rtA_allow Σ) m -> ART_A Σ m.
Proof. intros. unfold ART_A. repeat (split; [assumption|]). assumption. Qed.
