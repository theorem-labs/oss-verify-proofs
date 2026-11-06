(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require NodesA_madv.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition cpw (c i : Z) : word := Z_to_bv 64 ((i * ClassSize c) / 16).

Definition icells_rep (L : layoutA) (m : mem) : Prop :=
  rw_cells bsegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)]
  /\ ro_cells bsegs m 0x21489d [C1 (Z_to_bv 8 0)] /\ ro_cells bsegs m 0x2148a4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x178e28 [C8 (Z_to_bv 64 0x180478)] /\ ro_cells bsegs m 0x178e58 [C8 (Z_to_bv 64 0x17ae60)]
  /\ ro_cells bsegs m 0x17ae60 [C8 (Z_to_bv 64 0x16b0b0)] /\ ro_cells bsegs m 0x180495 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x18397c [C4 (Z_to_bv 64 30)] /\ ro_cells bsegs m 0x2147ca [C1 (Z_to_bv 8 1)]

  /\ ro_cells bsegs m 0x179bd8 [C8 (Z_to_bv 64 0x6d6ee8)] /\ ro_cells bsegs m 0x179bd8 [C8 (Z_to_bv 64 0x6d6ee8)]

  /\ ro_cells bsegs m 0x179998 [C8 (Z_to_bv 64 0x183959)] /\ ro_cells bsegs m 0x183959 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x17ae68 [C8 (Z_to_bv 64 0x16b4b4)] /\ ro_cells bsegs m 0x17aca0 [C8 (Z_to_bv 64 0x16afb4)]
  /\ ro_cells bsegs m 0x17ae10 [C8 (Z_to_bv 64 0x16bc98)] /\ ro_cells bsegs m 0x17ac68 [C8 (Z_to_bv 64 0x16b998)]
  /\ ro_cells bsegs m 0x2148a3 [C1 (Z_to_bv 8 1)]

  /\ rw_cells bsegs m 0x180438 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells bsegs m 0x180440 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells bsegs m 0x204ee2 [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0x2147ca [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x178e28 [C8 (Z_to_bv 64 0x180478)] /\ rw_cells bsegs m (0x180478 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m (0x180478 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells bsegs m (0x180478 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m (0x6b6ea8 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x179a90 [C8 (Z_to_bv 64 16)]
  /\ rw_cells bsegs m 0x214740 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x1824dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk bsegs m (l_T L + 2768) (l_T L + 3168)

  /\ rw_cells bsegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]

  /\ rw_cells bsegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells bsegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]

  /\ rw_cells bsegs m 0x178e70 [C8 (Z_to_bv 64 1)] /\ rw_cells bsegs m 0x214883 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x21489c [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0x179bd8 [C8 (Z_to_bv 64 0x6d6ee8)]
  /\ rw_cells bsegs m 0x6d7168 [C8 (Z_to_bv 64 4096)]

  /\ Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro

  /\ rw_cells bsegs m (l_T L + 72) [C8 (Z_to_bv 64 (l_FSB L))]
  /\ ro_cells bsegs m 0x17adf8 [C8 (Z_to_bv 64 0x151f50)].

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
  fs_gstate (frames Σ) (gcredit Σ) FSB m /\ fs_cls_rep FSB 5 (fs0 Σ) m /\ fs_cls_rep FSB 0 (fsc0 Σ) m /\ fs_cls_rep FSB 4 (fs4 Σ) m /\ fs_cls_rep FSB 1 (fs1 Σ) m
  /\ rw_cells bsegs m tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
  /\ (exists tb te, ttls_cells (l_T L) m tb te)
  /\ fs_busy L (frames Σ) m.

Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

Definition CS_W : list (Z * Z) :=
  [(0x17d378, 0x17d8a0); (0x17d960, 0x17f618); (0x6a52d0, 0x6b52d0); (0x6b52d0, 0x6b5330); (0x6b5360, 0x6b5368); (0x6b5380, 0x6b5388); (0x6b53a0, 0x6b53a8); (0x6b53c0, 0x6b53d0); (0x6b53e0, 0x6b53e8); (0x6b5400, 0x6b5408); (0x6b5420, 0x6b5450); (0x6b5480, 0x6b5488); (0x6b54a0, 0x6b6e50); (0x6b6e58, 0x6b6ea0); (0x6b6ec0, 0x6b6ec8); (0x6b6ed8, 0x6d7168); (0x6d7170, 0x6d8360); (0x6d8368, 0x6d8898)].

Definition CS_ACC : list (Z * Z) :=
  [(0x17d378, 0x17d8a0); (0x17d960, 0x17dd10); (0x17f590, 0x17f618); (0x6a52d0, 0x6b52d0); (0x6b52d0, 0x6b5330); (0x6b5360, 0x6b5368); (0x6b5380, 0x6b5388); (0x6b53a0, 0x6b53a8); (0x6b53c0, 0x6b53d0); (0x6b53e0, 0x6b53e8); (0x6b5400, 0x6b5408); (0x6b5420, 0x6b5450); (0x6b5480, 0x6b5488); (0x6b54a0, 0x6b6e50); (0x6b6e58, 0x6b6ea0); (0x6b6ec0, 0x6b6ec8); (0x6b6ed8, 0x6d7168); (0x6d7170, 0x6d8360); (0x6d8368, 0x6d8898);

   (0x238e0, 0x238e7); (0x23900, 0x2390d); (0x23920, 0x23923); (0x23940, 0x23943); (0x23960, 0x23965); (0x23980, 0x23994); (0x239c0, 0x239c4); (0x239e0, 0x239e2); (0x23a00, 0x23a02); (0x23a40, 0x23a44); (0x23a60, 0x23a71); (0x23aa0, 0x23aba); (0x23ae0, 0x23ae9); (0x23b00, 0x23b09); (0x23b20, 0x23b22); (0x23b40, 0x23b52); (0x23b80, 0x23b87); (0x23ba0, 0x23ba6); (0x23bc0, 0x23bc6); (0x23be0, 0x23be7); (0x23c00, 0x23c25); (0x23c60, 0x23c80); (0x23ca0, 0x23cb2); (0x23ce0, 0x23d09); (0x23d40, 0x23d57); (0x23d80, 0x23da5); (0x23de0, 0x23e09); (0x23e40, 0x23e48); (0x23e60, 0x23e6f); (0x23e80, 0x23e83); (0x23ea0, 0x23ea3); (0x23ec0, 0x23ec3); (0x23ee0, 0x23ee3); (0x23f00, 0x23f03); (0x23f20, 0x23f23); (0x24540, 0x24552); (0x24580, 0x245b8); (0x245e0, 0x24623); (0x24660, 0x246fd); (0x24720, 0x24771); (0x247a0, 0x247cd); (0x24800, 0x24849); (0x24880, 0x248c9); (0x24900, 0x24949); (0x24980, 0x249ad); (0x249e0, 0x24a29); (0x24a60, 0x24a89); (0x24ac0, 0x24add); (0x24b00, 0x24b15); (0x24b40, 0x24ba0); (0x24bc0, 0x24bf7); (0x24c20, 0x24ccc); (0x24d00, 0x24d43); (0x24d80, 0x24de1); (0x24e20, 0x24e7f); (0x24ea0, 0x24ee8); (0x24f20, 0x24f42); (0x24f80, 0x24fb3); (0x24fe0, 0x25013); (0x25040, 0x250ac); (0x250e0, 0x2512d); (0x25160, 0x251c1); (0x25200, 0x252cf); (0x25300, 0x25384); (0x253c0, 0x25471); (0x254a0, 0x254df); (0x25500, 0x25541); (0x25580, 0x255ce); (0x25600, 0x25700); (0x25740, 0x26518); (0x26880, 0x26938); (0x26960, 0x29210); (0x29c40, 0x29c49); (0x29c60, 0x29c85); (0x29ce0, 0x29d10); (0x29d80, 0x29d8c); (0x29da0, 0x29dd0); (0x29e40, 0x29e60); (0x29e80, 0x29f80); (0x29fc0, 0x2a0c0); (0x2c9c0, 0x2ca60); (0x2cd00, 0x2cd01); (0x2cd20, 0x2cd21); (0x173360, 0x173570); (0x173600, 0x173640); (0x173660, 0x173678); (0x1736c0, 0x173720); (0x173740, 0x173758); (0x2a100, 0x2c9b0); (0x2ca80, 0x2cd00); (0x34858, 0x34888); (0x173228, 0x173240); (0x176c50, 0x176c58);

   (0x10e0d, 0x10e17); (0x1504b, 0x1504f); (0x163c0, 0x16440); (0x163ee, 0x163ff); (0x1aeb9, 0x1aeda); (0x1f625, 0x1f63a); (0x1f63a, 0x1f651);
   (0x21e00, 0x21e80); (0x22ff0, 0x22ff7); (0x22ff0, 0x22ff7); (0x34ef0, 0x34f00); (0x6a52c0, 0x6a52d0);
     (0x13f9b, 0x13fae); (0x14aa3, 0x14aa4); (0x17f05, 0x17f08); (0x1a612, 0x1a615); (0x200a9, 0x200ac); (0x20d2b, 0x20d2e)].

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
