(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require NodesA_madv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition cpw (c i : Z) : word := Z_to_bv 64 ((i * ClassSize c) / 16).

Definition icells_rep (L : layoutA) (m : mem) : Prop :=
  rw_cells asegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs m 0x20585d [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x205864 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x16a228 [C8 (Z_to_bv 64 0x171438)] /\ ro_cells asegs m 0x16a258 [C8 (Z_to_bv 64 0x16c248)]
  /\ ro_cells asegs m 0x16c248 [C8 (Z_to_bv 64 0x15c524)] /\ ro_cells asegs m 0x171455 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x17493c [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x20578a [C1 (Z_to_bv 8 1)]

  /\ ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)] /\ ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)]

  /\ ro_cells asegs m 0x16ad98 [C8 (Z_to_bv 64 0x174919)] /\ ro_cells asegs m 0x174919 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x16c250 [C8 (Z_to_bv 64 0x15c928)] /\ ro_cells asegs m 0x16c088 [C8 (Z_to_bv 64 0x15c428)]
  /\ ro_cells asegs m 0x16c1f8 [C8 (Z_to_bv 64 0x15d10c)] /\ ro_cells asegs m 0x16c050 [C8 (Z_to_bv 64 0x15ce0c)]
  /\ ro_cells asegs m 0x205863 [C1 (Z_to_bv 8 1)]

  /\ rw_cells asegs m 0x1713f8 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0x171400 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x1f5ea2 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x20578a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x16a228 [C8 (Z_to_bv 64 0x171438)] /\ rw_cells asegs m (0x171438 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0x171438 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0x171438 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x6a7e68 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x16ae90 [C8 (Z_to_bv 64 16)]
  /\ rw_cells asegs m 0x205700 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x17349c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)

  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]

  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]

  /\ rw_cells asegs m 0x16a270 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x205843 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x20585c [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)]
  /\ rw_cells asegs m 0x6c8128 [C8 (Z_to_bv 64 4096)]

  /\ Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro

  /\ rw_cells asegs m (l_T L + 72) [C8 (Z_to_bv 64 (l_FSB L))]
  /\ ro_cells asegs m 0x16c1e0 [C8 (Z_to_bv 64 0x1433c4)].

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

Definition pshadow_allocA (an : option Z) (m : mem) (AB S n : Z) : Prop :=
  bytes_at asegs m (shad AB) (farun (rz_size n / 8) ++ ushadowA an n)
  /\ bytes_at asegs m (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)).
Definition pchunk (A : list (Z * Z * Z)) (SB c : Z) (i : nat) (st : ckst) (m : mem) : Prop :=
  let AB := p_abeg SB c i in let S := ClassSize c in
  match st with
  | CkIdle => stk asegs m AB (AB + S) /\ pshadow_idle m AB S
  | CkBatch => pshadow_idle m AB S
  | CkAlloc n => wr_at asegs m AB S /\ ahdr m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                 /\ pshadow_allocA (alook (AB + rz_size n) n A) m AB S n
  | CkQuar n => wr_at asegs m AB S /\ qhdr3 m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                /\ pshadow_quar m AB S n
  end.

Definition schunk (A : list (Z * Z * Z)) (k : nat) (s : secst) (m : mem) : Prop :=
  let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
  shdr m mb msz (needed n + rz_size n) (Z.of_nat k) /\ wr_at asegs m mb msz /\ lch m AB M
  /\ (if s_quar s then qhdr3 m M n else ahdr m M n)
  /\ stk asegs m (shad mb) (shad (mb + msz))
  /\ bytes_at asegs m (shad mb) (farun ((4096 + 2048) / 8))
  /\ bytes_at asegs m (shad (AB + 2048)) (if s_quar s then fdrun (ru8 n / 8) else ushadowA (alook (AB + 2048) n A) n)
  /\ bytes_at asegs m (shad (AB + 2048 + ru8 n)) (farun ((msz - 4096 - 2048 - ru8 n) / 8)).
Definition chunk_rep (Σ : rtsA) (m : mem) : Prop :=
  (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk (ann Σ) (l_SB (lay Σ)) c i st m)
  /\ (forall k s, nth_error (sec Σ) k = Some s -> schunk (ann Σ) k s m).

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

Definition gcredit (Σ : rtsA) : Z := if gw then credit Σ else 0.
Definition fs_rep (Σ : rtsA) (m : mem) : Prop :=
  let L := lay Σ in let FSB := l_FSB L in
  fs_gstate (frames Σ) (gcredit Σ) FSB m /\ fs_cls_rep FSB 5 (fs0 Σ) m /\ fs_cls_rep FSB 0 (fsc0 Σ) m /\ fs_cls_rep FSB 4 (fs4 Σ) m /\ fs_cls_rep FSB 1 (fs1 Σ) m
  /\ rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
  /\ (exists tb te, ttls_cells (l_T L) m tb te)
  /\ fs_busy L (frames Σ) m.

Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

Definition CS_W : list (Z * Z) :=
  [(0x16e760, 0x1705d8); (0x696290, 0x6a6290); (0x6a6290, 0x6a62f0); (0x6a6320, 0x6a6328); (0x6a6340, 0x6a6348); (0x6a6360, 0x6a6368); (0x6a6380, 0x6a6390); (0x6a63a0, 0x6a63a8); (0x6a63c0, 0x6a63c8); (0x6a63e0, 0x6a6410); (0x6a6440, 0x6a6448); (0x6a6460, 0x6a7e10); (0x6a7e18, 0x6a7e60); (0x6a7e80, 0x6a7e88); (0x6a7e98, 0x6c8128); (0x6c8130, 0x6c9320); (0x6c9328, 0x6c9858)].

Definition CS_ACC : list (Z * Z) :=
  [(0x16e760, 0x16ed30); (0x170570, 0x1705d8); (0x696290, 0x6a6290); (0x6a6290, 0x6a62f0); (0x6a6320, 0x6a6328); (0x6a6340, 0x6a6348); (0x6a6360, 0x6a6368); (0x6a6380, 0x6a6390); (0x6a63a0, 0x6a63a8); (0x6a63c0, 0x6a63c8); (0x6a63e0, 0x6a6410); (0x6a6440, 0x6a6448); (0x6a6460, 0x6a7e10); (0x6a7e18, 0x6a7e60); (0x6a7e80, 0x6a7e88); (0x6a7e98, 0x6c8128); (0x6c8130, 0x6c9320); (0x6c9328, 0x6c9858);

   (0x23700, 0x23707); (0x23720, 0x2372d); (0x23740, 0x23743); (0x23760, 0x23763); (0x23780, 0x23785); (0x237a0, 0x237b4); (0x237e0, 0x237e4); (0x23800, 0x23802); (0x23820, 0x23822); (0x23860, 0x23864); (0x23880, 0x23891); (0x238c0, 0x238da); (0x23900, 0x23909); (0x23920, 0x23929); (0x23940, 0x23942); (0x23960, 0x23972); (0x239a0, 0x239a7); (0x239c0, 0x239c6); (0x239e0, 0x239e6); (0x23a00, 0x23a07); (0x23a20, 0x23a45); (0x23a80, 0x23aa0); (0x23ac0, 0x23ad2); (0x23b00, 0x23b29); (0x23b60, 0x23b77); (0x23ba0, 0x23bc5); (0x23c00, 0x23c29); (0x23c60, 0x23c68); (0x23c80, 0x23c8f); (0x23ca0, 0x23ca3); (0x23cc0, 0x23cc3); (0x23ce0, 0x23ce3); (0x23d00, 0x23d03); (0x23d20, 0x23d23); (0x23d40, 0x23d43); (0x24360, 0x24372); (0x243a0, 0x243d8); (0x24400, 0x24443); (0x24480, 0x2451d); (0x24540, 0x24591); (0x245c0, 0x245ed); (0x24620, 0x24669); (0x246a0, 0x246e9); (0x24720, 0x24769); (0x247a0, 0x247cd); (0x24800, 0x24849); (0x24880, 0x248a9); (0x248e0, 0x248fd); (0x24920, 0x24935); (0x24960, 0x249c0); (0x249e0, 0x24a17); (0x24a40, 0x24aec); (0x24b20, 0x24b63); (0x24ba0, 0x24c01); (0x24c40, 0x24c9f); (0x24cc0, 0x24d08); (0x24d40, 0x24d62); (0x24da0, 0x24dd3); (0x24e00, 0x24e33); (0x24e60, 0x24ecc); (0x24f00, 0x24f4d); (0x24f80, 0x24fe1); (0x25020, 0x250ef); (0x25120, 0x251a4); (0x251e0, 0x25291); (0x252c0, 0x252ff); (0x25320, 0x25361); (0x253a0, 0x253ee); (0x25420, 0x25520); (0x25560, 0x26338); (0x266a0, 0x26758); (0x26780, 0x29030); (0x29a60, 0x29a69); (0x29a80, 0x29d80); (0x29e40, 0x29e65); (0x29ec0, 0x29ef0); (0x29f60, 0x29f6c); (0x29f80, 0x29fb0); (0x2a020, 0x2a040); (0x2a060, 0x2a160); (0x2a1a0, 0x2a2a0); (0x2cba0, 0x2cc40); (0x2cee0, 0x2cee1); (0x164760, 0x164970); (0x164a00, 0x164a40); (0x164a60, 0x164a78); (0x164ac0, 0x164b20); (0x164b40, 0x164b58); (0x2a2e0, 0x2cb90); (0x2cc60, 0x2cee0); (0x34a18, 0x34a48); (0x164628, 0x164640); (0x168050, 0x168058);

   (0x10dd9, 0x10de3); (0x14ffe, 0x15002); (0x16380, 0x16400); (0x16390, 0x163a1); (0x1ae0b, 0x1ae2c); (0x1f5f2, 0x1f607); (0x1f607, 0x1f61e);
   (0x21d40, 0x21dc0); (0x22e7d, 0x22e84); (0x22e7d, 0x22e84); (0x350b0, 0x350c0); (0x696280, 0x696290);
     (0x13f46, 0x13f59); (0x14a56, 0x14a57); (0x17e6d, 0x17e70); (0x1a564, 0x1a567); (0x1ffdd, 0x1ffe0); (0x20c56, 0x20c59)].

Definition static_acc (m : mem) : Prop := Forall (fun r => acc asegs m (fst r) (snd r - fst r)) CS_ACC.

Definition shadow_rep (L : layoutA) (m : mem) : Prop :=
  bytes_at asegs m (shad (l_ACEIL L)) (zrun ((2 ^ 47 - l_ACEIL L) / 8))
  /\ stk asegs m (shad (l_ACEIL L)) (shad (2 ^ 47))
  /\ stk asegs m (pg_dn (shad 0x10000)) (shad SEGTOP_A)
  /\ static_acc m

  /\ stk asegs m (l_ACEIL L) (l_top L).

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
  Permutation (List.filter vpos (vm_maps (m_vmmaps mo))) (rt_maps Σ) /\ vm_reserved (m_vmmaps mo) = segments_reserved asegs
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
