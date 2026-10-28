(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require NodesA_madv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Definition cpw (c i : Z) : word := Z_to_bv 64 ((i * ClassSize c) / 16).

Definition Z15 : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition mtab_rep (L : layoutA) (m : mem) : Prop :=
  rw_cells bsegs m 0x1891c0 [C8 (Z_to_bv 64 0x1891c8)] /\ rw_cells bsegs m 0x1891c8 [C8 (Z_to_bv 64 (l_MT L))]
  /\ rw_cells bsegs m (l_MT L + 0x24798) Z15 /\ rw_cells bsegs m (l_MT L + 0x1b5760) Z15.

Definition icells_rep (L : layoutA) (m : mem) : Prop :=
  rw_cells bsegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)]
  /\ ro_cells bsegs m 0x21b59d [C1 (Z_to_bv 8 0)] /\ ro_cells bsegs m 0x21b5a4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x17fec0 [C8 (Z_to_bv 64 0x187178)] /\ ro_cells bsegs m 0x17fef0 [C8 (Z_to_bv 64 0x181f38)]
  /\ ro_cells bsegs m 0x181f38 [C8 (Z_to_bv 64 0x171db0)] /\ ro_cells bsegs m 0x187195 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x18a67c [C4 (Z_to_bv 64 30)] /\ ro_cells bsegs m 0x21b4ca [C1 (Z_to_bv 8 1)]

  /\ ro_cells bsegs m 0x180cb8 [C8 (Z_to_bv 64 0x6de428)] /\ ro_cells bsegs m 0x180cb8 [C8 (Z_to_bv 64 0x6de428)]

  /\ ro_cells bsegs m 0x180a30 [C8 (Z_to_bv 64 0x18a659)] /\ ro_cells bsegs m 0x18a659 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x181f40 [C8 (Z_to_bv 64 0x1721b4)] /\ ro_cells bsegs m 0x181d78 [C8 (Z_to_bv 64 0x171cb4)]
  /\ ro_cells bsegs m 0x181ee8 [C8 (Z_to_bv 64 0x1728e4)] /\ ro_cells bsegs m 0x181d48 [C8 (Z_to_bv 64 0x1726a4)]
  /\ ro_cells bsegs m 0x21b5a3 [C1 (Z_to_bv 8 1)]

  /\ rw_cells bsegs m 0x187138 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells bsegs m 0x187140 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells bsegs m 0x20bbe2 [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0x21b4ca [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x17fec0 [C8 (Z_to_bv 64 0x187178)] /\ rw_cells bsegs m (0x187178 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m (0x187178 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells bsegs m (0x187178 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m (0x6be3e8 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x180b28 [C8 (Z_to_bv 64 16)]
  /\ rw_cells bsegs m 0x21b440 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x1891dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk bsegs m (l_T L + 2768) (l_T L + 3168)

  /\ rw_cells bsegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]

  /\ rw_cells bsegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells bsegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]

  /\ rw_cells bsegs m 0x17ff08 [C8 (Z_to_bv 64 1)] /\ rw_cells bsegs m 0x21b583 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x21b59c [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0x180cb8 [C8 (Z_to_bv 64 0x6de428)]
  /\ rw_cells bsegs m 0x6de6a8 [C8 (Z_to_bv 64 4096)]

  /\ mtab_rep L m
  /\ Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro

  /\ rw_cells bsegs m (l_T L + 72) [C8 (Z_to_bv 64 (l_FSB L))]
  /\ ro_cells bsegs m 0x181ed0 [C8 (Z_to_bv 64 0x158680)].

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

Definition pshadow_allocA (an : option Z) (m : mem) (AB S n : Z) : Prop :=
  bytes_at bsegs m (shad AB) (farun (rz_size n / 8) ++ ushadowA an n)
  /\ bytes_at bsegs m (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)).
Definition pchunk (A : list (Z * Z * Z)) (SB c : Z) (i : nat) (st : ckst) (m : mem) : Prop :=
  let AB := p_abeg SB c i in let S := ClassSize c in
  match st with
  | CkIdle => stk bsegs m AB (AB + S) /\ pshadow_idle m AB S
  | CkBatch => pshadow_idle m AB S
  | CkAlloc n => wr_at bsegs m AB S /\ ahdr m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                 /\ pshadow_allocA (alook (AB + rz_size n) n A) m AB S n
  | CkQuar n => wr_at bsegs m AB S /\ qhdr3 m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                /\ pshadow_quar m AB S n
  end.

Definition schunk (A : list (Z * Z * Z)) (k : nat) (s : secst) (m : mem) : Prop :=
  let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
  shdr m mb msz (needed n + rz_size n) (Z.of_nat k) /\ wr_at bsegs m mb msz /\ lch m AB M
  /\ (if s_quar s then qhdr3 m M n else ahdr m M n)
  /\ stk bsegs m (shad mb) (shad (mb + msz))
  /\ bytes_at bsegs m (shad mb) (farun ((4096 + 2048) / 8))
  /\ bytes_at bsegs m (shad (AB + 2048)) (if s_quar s then fdrun (ru8 n / 8) else ushadowA (alook (AB + 2048) n A) n)
  /\ bytes_at bsegs m (shad (AB + 2048 + ru8 n)) (farun ((msz - 4096 - 2048 - ru8 n) / 8)).
Definition chunk_rep (Σ : rtsA) (m : mem) : Prop :=
  (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk (ann Σ) (l_SB (lay Σ)) c i st m)
  /\ (forall k s, nth_error (sec Σ) k = Some s -> schunk (ann Σ) k s m).

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

Definition gcredit (Σ : rtsA) : Z := if gw then credit Σ else 0.
Definition fs_rep (Σ : rtsA) (m : mem) : Prop :=
  let L := lay Σ in let FSB := l_FSB L in
  fs_gstate (frames Σ) (gcredit Σ) FSB m /\ fs_cls_rep FSB 5 (fs0 Σ) m /\ fs_cls_rep FSB 0 (fsc0 Σ) m /\ fs_cls_rep FSB 4 (fs4 Σ) m /\ fs_cls_rep FSB 1 (fs1 Σ) m /\ fs_cls_rep FSB 3 (fs3 Σ) m /\ fs_cls_rep FSB 2 (fs2 Σ) m
  /\ rw_cells bsegs m tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
  /\ (exists tb te, ttls_cells (l_T L) m tb te)
  /\ fs_busy L (frames Σ) m.

Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

Definition CS_W : list (Z * Z) :=
  [(0x184450, 0x184980); (0x184a40, 0x186318); (0x6abfd0, 0x6bbfd0); (0x6bbfd0, 0x6bc018); (0x6bc040, 0x6bc048); (0x6bc060, 0x6bc090); (0x6bc0c0, 0x6bc0c8); (0x6bc0e0, 0x6bc0e1); (0x6bc100, 0x6bc108); (0x6bc120, 0x6bc128); (0x6bc140, 0x6bc148); (0x6bc160, 0x6bc170); (0x6bc180, 0x6bc188); (0x6bc1a0, 0x6bc1a8); (0x6bc1c0, 0x6bc1f0); (0x6bc220, 0x6bc228); (0x6bc240, 0x6be390); (0x6be398, 0x6be3e0); (0x6be400, 0x6be408); (0x6be418, 0x6de6a8); (0x6de6b0, 0x6df8a0); (0x6df8a8, 0x6dfdd8)].

Definition CS_ACC : list (Z * Z) :=
  [(0x184450, 0x184980); (0x184a40, 0x184df0); (0x1862b0, 0x186318); (0x6abfd0, 0x6bbfd0); (0x6bbfd0, 0x6bc018); (0x6bc040, 0x6bc048); (0x6bc060, 0x6bc090); (0x6bc0c0, 0x6bc0c8); (0x6bc0e0, 0x6bc0e1); (0x6bc100, 0x6bc108); (0x6bc120, 0x6bc128); (0x6bc140, 0x6bc148); (0x6bc160, 0x6bc170); (0x6bc180, 0x6bc188); (0x6bc1a0, 0x6bc1a8); (0x6bc1c0, 0x6bc1f0); (0x6bc220, 0x6bc228); (0x6bc240, 0x6be390); (0x6be398, 0x6be3e0); (0x6be400, 0x6be408); (0x6be418, 0x6de6a8); (0x6de6b0, 0x6df8a0); (0x6df8a8, 0x6dfdd8);

   (0x23980, 0x23987); (0x239a0, 0x239ad); (0x239c0, 0x239c3); (0x239e0, 0x239e3); (0x23a00, 0x23a05); (0x23a20, 0x23a25); (0x23a40, 0x23a46); (0x23a60, 0x23a64); (0x23c80, 0x23c91); (0x23cc0, 0x23cc8); (0x23ce0, 0x23cea); (0x23d00, 0x23d10); (0x23d20, 0x23d26); (0x23d40, 0x23d48); (0x23d60, 0x23d6f); (0x24380, 0x24392); (0x243c0, 0x243f8); (0x24420, 0x24463); (0x244a0, 0x2453d); (0x24560, 0x245b1); (0x245e0, 0x2460d); (0x24640, 0x24689); (0x246c0, 0x24709); (0x24740, 0x24789); (0x247c0, 0x247ed); (0x24820, 0x24869); (0x248a0, 0x248c9); (0x24900, 0x2491d); (0x24940, 0x24955); (0x24980, 0x249e0); (0x24a00, 0x24a37); (0x24a60, 0x24b0c); (0x24b40, 0x24b83); (0x24bc0, 0x24c21); (0x24c60, 0x24cbf); (0x24ce0, 0x24d28); (0x24d60, 0x24d82); (0x24dc0, 0x24df3); (0x24e20, 0x24e53); (0x24e80, 0x24eec); (0x24f20, 0x24f6d); (0x24fa0, 0x25001); (0x25040, 0x2510f); (0x25140, 0x251c4); (0x25200, 0x252b1); (0x252e0, 0x2531f); (0x25340, 0x25381); (0x253c0, 0x2540e); (0x25440, 0x25540); (0x25580, 0x26358); (0x266c0, 0x26778); (0x267a0, 0x29050); (0x29a80, 0x29a89); (0x29aa0, 0x29ac5); (0x29b20, 0x29b50); (0x29c80, 0x2c330); (0x2cce0, 0x2ccec); (0x2cd00, 0x2cd30); (0x2cda0, 0x2cdc0); (0x2cde0, 0x2cee0); (0x2cf20, 0x2d020); (0x2f920, 0x2f9c0); (0x2fc60, 0x2fc61); (0x2fc80, 0x2fc81); (0x179de0, 0x179ff0); (0x17a080, 0x17a0c0); (0x17a0e0, 0x17a0f8); (0x17a140, 0x17a1a0); (0x17a1c0, 0x17a1d8); (0x184680, 0x184980); (0x2d060, 0x2f910); (0x2f9e0, 0x2fc60); (0x37998, 0x379c8); (0x17dce0, 0x17dce8); (0x23a80, 0x23c80); (0x29bb0, 0x29c78); (0x17d7a0, 0x17d7a8); (0x17d8b8, 0x17d8c0); (0x17d908, 0x17d930);

   (0x10e24, 0x10e2e); (0x15046, 0x1504a); (0x16400, 0x16480); (0x16412, 0x16423); (0x1ae83, 0x1aea4); (0x1f63a, 0x1f64f); (0x1f64f, 0x1f666);
   (0x21ec0, 0x21f40); (0x23192, 0x23199); (0x23192, 0x23199); (0x38030, 0x38040); (0x6abfc0, 0x6abfd0);
     (0x13f96, 0x13fa9); (0x14a9e, 0x14a9f); (0x17eff, 0x17f02); (0x1a5dc, 0x1a5df); (0x200fe, 0x20101); (0x20df7, 0x20dfa)].

Definition static_acc (m : mem) : Prop := Forall (fun r => acc bsegs m (fst r) (snd r - fst r)) CS_ACC.

Definition shadow_rep (L : layoutA) (m : mem) : Prop :=
  bytes_at bsegs m (shad (l_ACEIL L)) (zrun ((2 ^ 47 - l_ACEIL L) / 8))
  /\ stk bsegs m (shad (l_ACEIL L)) (shad (2 ^ 47))
  /\ stk bsegs m (pg_dn (shad 0x10000)) (shad SEGTOP_A)
  /\ static_acc m

  /\ stk bsegs m (l_ACEIL L) (l_top L).

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
  /\ dep_rep (lay Σ) (dep Σ) m /\ fs_rep Σ m /\ ia_rep Σ m /\ shadow_rep (lay Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

Definition lazy_in_maps_A (mo : Model) : Prop :=
  forall iv, In iv (m_vm_lazy mo) -> 0 < bv_unsigned (snd iv) ->
    exists e, In e (vm_maps (m_vmmaps mo)) /\ bv_unsigned (fst e) <= bv_unsigned (fst iv)
              /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e) + bv_unsigned (snd e).
Definition iv_apart (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Definition confined0 (Σ : rtsA) (mo : Model) : Prop :=
  forall z, BackingAlgebra.covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) z = true -> BackingAlgebra.covered (l_maps0 (lay Σ)) z = true.

Definition shadow_lazy (mo : Model) : Prop :=
  forall a : word, shreg (bv_unsigned a) ->
    page_in_ranges (page_base a) (m_vm_lazy mo) = true /\ BackingAlgebra.covered (vm_noaccess (m_vmmaps mo)) (bv_unsigned a) = false.

Definition maps_zbound (mo : Model) : Prop :=
  Z.of_nat (length (vm_maps (m_vmmaps mo))) <= Z.of_nat (length (List.filter vpos (vm_maps (m_vmmaps mo)))) + 1.
Definition artm_sys (Σ : rtsA) (mo : Model) : Prop :=
  BackingAlgebra.model_ivs_wf mo /\ lazy_in_maps_A mo /\ ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo))
  /\ bv_unsigned (vm_init_sp (m_vmmaps mo)) = l_sp0 (lay Σ) /\ confined0 Σ mo /\ shadow_lazy mo /\ maps_zbound mo

  /\ NodesA_madv.noaccess_pos mo.

Definition ARTM_A (Σ : rtsA) (mo : Model) : Prop :=
  Permutation (List.filter vpos (vm_maps (m_vmmaps mo))) (rt_maps Σ) /\ vm_reserved (m_vmmaps mo) = segments_reserved bsegs
  /\ vm_limit (m_vmmaps mo) = VMLIMIT /\ eager_used mo <= E0_MAX + rt_eager Σ /\ artm_sys Σ mo.

Definition RTA : rt_sig := mkRTS rtsA ART_A ARTM_A rtA_live rtA_frames rtA_allow rtA_sp0 rtA_credit.

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

Lemma covered_filter_vpos : forall (l : list (word * word)) (z : Z), BackingAlgebra.covered (List.filter vpos l) z = BackingAlgebra.covered l z.
Proof.
  intros l z. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter]. destruct (vpos e) eqn:Ev.
  - unfold BackingAlgebra.covered in *. cbn [existsb]. rewrite IH. reflexivity.
  - unfold BackingAlgebra.covered in *. cbn [existsb]. rewrite IH. unfold vpos in Ev. apply Z.ltb_ge in Ev.
    pose proof (bv_unsigned_in_range _ (snd e)) as Hr. unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S.
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
Lemma ART_shadow : shadow_rep (lay Σ) m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
Lemma ART_vis : vis_rep (lay Σ) (rtA_allow Σ) m. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
End Proj.

Lemma ART_intro : forall Σ m, rt_wf Σ -> consts_rep (lay Σ) m -> prim_rep Σ m -> cache_rep Σ m -> chunk_rep Σ m ->
  sec_rep Σ m -> quar_rep Σ m -> dep_rep (lay Σ) (dep Σ) m -> fs_rep Σ m -> ia_rep Σ m -> shadow_rep (lay Σ) m ->
  vis_rep (lay Σ) (rtA_allow Σ) m -> ART_A Σ m.
Proof. intros. unfold ART_A. repeat (split; [assumption|]). assumption. Qed.

Lemma pchunk_annbr : forall (A A' : list (Z * Z * Z)) SB c i st (m : mem),
  (forall n, st = CkAlloc n -> alook (p_abeg SB c i + rz_size n) n A' = alook (p_abeg SB c i + rz_size n) n A) ->
  pchunk A SB c i st m -> pchunk A' SB c i st m.
Proof. intros A A' SB c i st m H P. unfold pchunk in *. destruct st as [|n|n|]; try exact P. unfold pshadow_allocA in *. rewrite (H n eq_refl). exact P. Qed.
Lemma schunk_annbr : forall (A A' : list (Z * Z * Z)) k s (m : mem),
  alook (s_mb s + 4096 + 2048) (s_n s) A' = alook (s_mb s + 4096 + 2048) (s_n s) A -> schunk A k s m -> schunk A' k s m.
Proof. intros A A' k s m H P. unfold schunk in *. rewrite H. exact P. Qed.

End GWIN.
