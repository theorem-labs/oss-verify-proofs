(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.openssl.ct.lib.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Mem Frame Cells Step Arr RzCPS. 
From OSSVerify.Proofs.openssl.ct.lib.Lib Require NodesA_madv.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Export LibSh.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cpw (c i : Z) : word := Z_to_bv 64 ((i * ClassSize c) / 16).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition icells_rep (L : layoutA) (m : mem) : Prop :=
  rw_cells ctbsegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)]
  /\ ro_cells ctbsegs m 0x736a9d [C1 (Z_to_bv 8 0)] /\ ro_cells ctbsegs m 0x736aa4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells ctbsegs m 0x5e1b30 [C8 (Z_to_bv 64 0x6a2678)] /\ ro_cells ctbsegs m 0x5e1b60 [C8 (Z_to_bv 64 0x5e4da8)]
  /\ ro_cells ctbsegs m 0x5e4da8 [C8 (Z_to_bv 64 0x563e30)] /\ ro_cells ctbsegs m 0x6a2695 [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctbsegs m 0x6a5b7c [C4 (Z_to_bv 64 30)] /\ ro_cells ctbsegs m 0x7369ca [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells ctbsegs m 0x5e3ae8 [C8 (Z_to_bv 64 0xbfc270)] /\ ro_cells ctbsegs m 0x5e3ae8 [C8 (Z_to_bv 64 0xbfc270)]
  (* [comment removed for export] *)
  /\ ro_cells ctbsegs m 0x5e26c0 [C8 (Z_to_bv 64 0x6a5b59)] /\ ro_cells ctbsegs m 0x6a5b59 [C1 (Z_to_bv 8 1)]
  /\ ro_cells ctbsegs m 0x5e4db0 [C8 (Z_to_bv 64 0x564264)] /\ ro_cells ctbsegs m 0x5e4bd0 [C8 (Z_to_bv 64 0x563d34)]
  /\ ro_cells ctbsegs m 0x5e4d58 [C8 (Z_to_bv 64 0x564a04)] /\ ro_cells ctbsegs m 0x5e4b88 [C8 (Z_to_bv 64 0x564760)]
  /\ ro_cells ctbsegs m 0x736aa3 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells ctbsegs m 0x6a2638 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells ctbsegs m 0x6a2640 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells ctbsegs m 0x7270e2 [C1 (Z_to_bv 8 0)] /\ rw_cells ctbsegs m 0x7369ca [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctbsegs m 0x5e1b30 [C8 (Z_to_bv 64 0x6a2678)] /\ rw_cells ctbsegs m (0x6a2678 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells ctbsegs m (0x6a2678 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells ctbsegs m (0x6a2678 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctbsegs m (0xbdc230 + 32) [C4 (Z_to_bv 64 0)] /\ rw_cells ctbsegs m 0x5e27b0 [C8 (Z_to_bv 64 32)]
  /\ rw_cells ctbsegs m 0x736940 [C8 (Z_to_bv 64 0)] /\ rw_cells ctbsegs m 0x6a46dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctbsegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk ctbsegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells ctbsegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells ctbsegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells ctbsegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells ctbsegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells ctbsegs m 0x5e1b78 [C8 (Z_to_bv 64 1)] /\ rw_cells ctbsegs m 0x736a83 [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctbsegs m 0x736a9c [C1 (Z_to_bv 8 1)] /\ rw_cells ctbsegs m 0x5e3ae8 [C8 (Z_to_bv 64 0xbfc270)]
  /\ rw_cells ctbsegs m 0xbfc4f0 [C8 (Z_to_bv 64 4096)]
  (* [comment removed for export] *)
  /\ ro_cells ctbsegs m 0x5e4d50 [C8 (Z_to_bv 64 0x5644b4)]
  (* [comment removed for export] *)
  /\ Forall (fun p => rw_cells ctbsegs m (fst p) (snd p)) io_rw /\ Forall (fun p => ro_cells ctbsegs m (fst p) (snd p)) io_ro.

(* [comment removed for export] *)
Definition consts_rep (L : layoutA) (m : mem) : Prop :=
  inst_cells (l_SB L) m /\ mm_gcells m /\ thread_cells (l_TCX L) (l_T L) m /\ m2s_cells m /\ ps_cells m
  /\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m /\ client_consts m /\ icells_rep L m.

(* [comment removed for export] *)
Definition reg_rep (SB c : Z) (r : regst) (m : mem) : Prop :=
  let R := rinfo (RIS_of SB) c in
  let auser := ClassSize c * Z.of_nat (length (r_st r)) in
  ri_lock m R 0 /\ ri_core m R (Z.of_nat (length (r_fl r))) (r_mfa r) auser (r_muser r)
  /\ (exists rand exh pad nal nfr r0 r1 r2 r3, ri_tail m R rand exh pad nal nfr r0 r1 r2 r3)
  /\ (exists ws, fl_arr m SB c ws /\ 4 * Z.of_nat (length ws) = r_mfa r /\ firstn (length (r_fl r)) ws = map (cpw c) (r_fl r))
  /\ stk ctbsegs m (rb SB c + auser) (rb SB c + r_muser r)
  /\ bytes_at ctbsegs m (shad (rb SB c + auser)) (farun ((r_muser r - auser) / 8))
  /\ stk ctbsegs m (shad (rb SB c)) (shad (rb SB c + 2 ^ 32)).
Definition prim_rep (Σ : rtsA) (m : mem) : Prop := forall c, 1 <= c <= 31 -> reg_rep (l_SB (lay Σ)) c (pr Σ c) m.

(* [comment removed for export] *)
Definition pclass_rep (T c : Z) (init : bool) (l : list Z) (m : mem) : Prop :=
  pc_cells m (pc_addr T c) (Z.of_nat (length l)) (if init then MaxCount c else 0) (if init then ClassSize c else 0)
  /\ exists chs, u32arr ctbsegs m (pc_addr T c + 16) chs /\ length chs = 16%nat /\ firstn (length l) chs = map (cpw c) l.
Definition cache_rep (Σ : rtsA) (m : mem) : Prop :=
  forall c, 1 <= c <= 31 -> pclass_rep (l_T (lay Σ)) c (ca_init Σ) (ca Σ c) m.

(* [comment removed for export] *)
Definition pchunk (SB c : Z) (i : nat) (st : ckst) (m : mem) : Prop :=
  let AB := p_abeg SB c i in let S := ClassSize c in
  match st with
  | CkIdle => stk ctbsegs m AB (AB + S) /\ pshadow_idle m AB S
  | CkBatch => pshadow_idle m AB S
  | CkAlloc n => wr_at ctbsegs m AB S /\ ahdr m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                 /\ pshadow_alloc m AB S n
  | CkQuar n => wr_at ctbsegs m AB S /\ qhdr3 m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                /\ pshadow_quar m AB S n
  end.
(* [comment removed for export] *)
Definition schunk (k : nat) (s : secst) (m : mem) : Prop :=
  let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
  shdr m mb msz (needed n + rz_size n) (Z.of_nat k) /\ wr_at ctbsegs m mb msz /\ lch m AB M
  /\ (if s_quar s then qhdr3 m M n else ahdr m M n)
  /\ stk ctbsegs m (shad mb) (shad (mb + msz))     (* [comment removed for export] *)
  /\ bytes_at ctbsegs m (shad mb) (farun ((4096 + 2048) / 8))
  /\ bytes_at ctbsegs m (shad (AB + 2048)) (if s_quar s then fdrun (ru8 n / 8) else ushadow n)
  /\ bytes_at ctbsegs m (shad (AB + 2048 + ru8 n)) (farun ((msz - 4096 - 2048 - ru8 n) / 8)).
Definition chunk_rep (Σ : rtsA) (m : mem) : Prop :=
  (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk (l_SB (lay Σ)) c i st m)
  /\ (forall k s, nth_error (sec Σ) k = Some s -> schunk k s m).

(* [comment removed for export] *)
Definition sec_rep (Σ : rtsA) (m : mem) : Prop :=
  sec_core m (l_PAB (lay Σ)) (sec_nres Σ) (Z.of_nat (length (sec Σ))) /\ sec_pad m
  /\ (exists ws, u64arr ctbsegs m (l_PAB (lay Σ)) ws /\ Z.of_nat (length ws) = sec_nres Σ
                 /\ firstn (length (sec Σ)) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ))
  /\ sec_page m /\ sec_range m (l_PAB (lay Σ)) /\ sec_junk m /\ name_cells m    (* [comment removed for export] *).

(* [comment removed for export] *)
Definition quar_rep (Σ : rtsA) (m : mem) : Prop :=
  qcache_rep m (qcacheT (l_T (lay Σ))) (ql Σ) /\ qcache_rep m i_q_global (qg Σ)
  /\ rw_cells ctbsegs m i_q_cmutex [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dep_rep (L : layoutA) (d : depot) (m : mem) : Prop := depot_rep d (DEP_BK (hash_of (d_hs d) 1)) (l_DNB L) (l_SSB L) m.

(* [comment removed for export] *)
Definition fs_cls_rep (FSB c : Z) (f : fsst) (m : mem) : Prop :=
  fs_hint FSB c m (fss_hint f) /\ fs_flags FSB c m (fss_flags f) /\ fs_free_frames FSB c m (fss_flags f).
(* [comment removed for export] *)
Definition fs_busy (L : layoutA) (frs : list (Z * nat)) (m : mem) : Prop :=
  Forall (fun fk => exists p, fst fk = frame_addr (l_FSB L) (Z.of_nat (snd fk)) p
            /\ wr_at ctbsegs m (fst fk) (fs_size (snd fk)) /\ wr_at ctbsegs m (shad (fst fk)) (fs_size (snd fk) / 8)
            /\ rw_cells ctbsegs m (fst fk + fs_size (snd fk) - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB L) (Z.of_nat (snd fk)) + p))]) frs.
Definition fs_rep (Σ : rtsA) (m : mem) : Prop :=
  let L := lay Σ in let FSB := l_FSB L in
  fs_const FSB m /\ fs_cls_rep FSB 0 (fs0 Σ) m /\ fs_cls_rep FSB 2 (fs2 Σ) m /\ (fs_cls_rep FSB 4 (fs4 Σ) m /\ fs_cls_rep FSB 1 (fs1 Σ) m /\ fs_cls_rep FSB 3 (fs3 Σ) m)
  /\ rw_cells ctbsegs m tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
  /\ (exists tb te, ttls_cells (l_T L) m tb te)
  /\ fs_busy L (frames Σ) m.

(* [comment removed for export] *)
Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

(* [comment removed for export] *)
Definition CS_W : list (Z * Z) :=
  [(0x5e74c8, 0x6a1818); (0xbc74d0, 0xbd74d0); (0xbd74d0, 0xbdc1d8); (0xbdc1e0, 0xbdc228); (0xbdc270, 0xbfc4f0); (0xbfc4f8, 0xbfd5d8); (0xbfd5e0, 0xbfdb10)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0x5e74c8, 0x5e74e0); (0x5e7fc0, 0x5e82e0); (0x6a17a0, 0x6a1818); (0xbc74d0, 0xbd74d0); (0xbd74d0, 0xbd7500); (0xbdb920, 0xbdc1d8); (0xbdc1e0, 0xbdc228); (0xbdc270, 0xbfc4f0); (0xbfc4f8, 0xbfd5d8); (0xbfd5e0, 0xbfdb10);
   (* [comment removed for export] *) (* [comment removed for export] *)
   (0x1f6b5, 0x1f6cd); (0x21205, 0x2121a); (0x214cc, 0x214e3); (0x40b06, 0x40b1d); (0x47a6e, 0x47a84); (0x4969e, 0x496ac); (0x49700, 0x49714); (0x49714, 0x4972d); (0x497a0, 0x497b8); (0x49818, 0x49829); (0x49920, 0x49931); (0x499e0, 0x499f5); (0x49aa0, 0x49ab1); (0x4a9c0, 0x4a9cd); (0x4a9de, 0x4a9ed); (0x4ad00, 0x4ad0f); (0x4b640, 0x4b652); (0x4c780, 0x4c799); (0x4c7b1, 0x4c7ca); (0x70f00, 0x70f17); (0x71000, 0x71017); (0x713a0, 0x713b5); (0x71536, 0x7154c); (0x71660, 0x71676); (0x71676, 0x7168f); (0x72360, 0x72377); (0x725dc, 0x725f3); (0x72640, 0x72657); (0x726e0, 0x726f4); (0x72a40, 0x72a57); (0x72aa0, 0x72ab7); (0x72bbc, 0x72bd3); (0x72ce0, 0x72cf7); (0x73a60, 0x73a70); (0x75ce0, 0x75cf5); (0x761e0, 0x761f6); (0x76940, 0x76956); (0x787e0, 0x787f7); (0xa23a0, 0xa23b6); (0xa4a40, 0xa4a53); (0xa4b60, 0xa4b73); (0xa4e80, 0xa4e93); (0xf5320, 0xf5337); (0xfff40, 0xfff53);
   (* [comment removed for export] *)
   (0x121f9, 0x12203); (0x1d956, 0x1d95a); (0x21175, 0x21186); (0x21180, 0x21200); (0x2efe0, 0x2f001); (0x3d286, 0x3d29b); (0x3d29b, 0x3d2b2); (0x44680, 0x44700); (0x48e5c, 0x48e63); (0x113cd0, 0x113ce0); (0xbc74c0, 0xbc74d0)].
(* [comment removed for export] *)
Definition SH_RNGS : list (Z * Z) := IMG_HULL :: CS_ACC.
(* [comment removed for export] *)
Definition static_acc (m : mem) : Prop := Forall (fun r => acc ctbsegs m (fst r) (snd r - fst r)) CS_ACC.

(* [comment removed for export] *)
Definition shadow_rep (L : layoutA) (m : mem) : Prop :=
  bytes_at ctbsegs m (shad (l_ACEIL L)) (zrun ((2 ^ 47 - l_ACEIL L) / 8))
  /\ stk ctbsegs m (shad (l_ACEIL L)) (shad (2 ^ 47))
  /\ stk ctbsegs m (pg_dn (shad 0x10000)) (shad SEGTOP_A)   (* [comment removed for export] *)
  /\ static_acc m
  /\ lib_sh m.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shreg (z : Z) : Prop := (SHB <= z < K_LOW_SHADOW_hi) \/ (K_HIGH_SHADOW_lo <= z < K_HIGH_SHADOW_hi).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition vis_rep (L : layoutA) (A : list (Z * Z)) (m : mem) : Prop :=
  forall a : word, shreg (bv_unsigned a) -> page_allowedb A (page_base a) = true ->
    bv_unsigned a < shad (pg_dn (l_ACEIL L)) ->
    (forall e, In e (l_maps0 L) -> ~ (shad (bv_unsigned (fst e)) <= bv_unsigned a < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
    m a <> None.

(* [comment removed for export] *)
Lemma vis_rep_wmono : forall {L} A (m m' : mem), vis_rep L A m -> wmono ctbsegs m m' -> vis_rep L A m'.
Proof.
  intros L A m m' H WM a Hs Hp Hlo Hx. pose proof (H a Hs Hp Hlo Hx) as Ha.
  assert (NS : find_segment ctbsegs (bv_unsigned a) 1 = None).
  { unfold ctbsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments.
    cbn [find_segment].
    unfold AsanUbsan.AsanUbsan_segment_000, AsanUbsan.AsanUbsan_segment_001,
      AsanUbsan.AsanUbsan_segment_002, AsanUbsan.AsanUbsan_segment_003.
    cbn [seg_base seg_size]. unfold shreg, SHB, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs.
    destruct Hs as [Hs|Hs];
      repeat match goal with |- context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]; cbn [andb] end; reflexivity. }
  assert (W0 : wview ctbsegs m a <> None) by (unfold wview; destruct (m a); [discriminate | congruence]).
  pose proof (WM a W0) as W1. unfold wview in W1. destruct (m' a) eqn:E; [discriminate|]. rewrite NS in W1. exact W1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ART_A (Σ : rtsA) (m : mem) : Prop :=
  rt_wf Σ /\ consts_rep (lay Σ) m /\ prim_rep Σ m /\ cache_rep Σ m /\ chunk_rep Σ m /\ sec_rep Σ m /\ quar_rep Σ m
  /\ dep_rep (lay Σ) (dep Σ) m /\ fs_rep Σ m /\ ia_rep Σ m /\ shadow_rep (lay Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

(* [comment removed for export] *)
Definition lazy_in_maps_A (mo : Model) : Prop :=
  forall iv, In iv (m_vm_lazy mo) -> 0 < bv_unsigned (snd iv) ->
    exists e, In e (vm_maps (m_vmmaps mo)) /\ bv_unsigned (fst e) <= bv_unsigned (fst iv)
              /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e) + bv_unsigned (snd e).
Definition iv_apart (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
(* [comment removed for export] *)
Definition confined0 (Σ : rtsA) (mo : Model) : Prop :=
  forall z, BackingAlgebra.covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) z = true -> BackingAlgebra.covered (l_maps0 (lay Σ)) z = true.
(* [comment removed for export] *)
Definition shadow_lazy (mo : Model) : Prop :=
  forall a : word, shreg (bv_unsigned a) ->
    page_in_ranges (page_base a) (m_vm_lazy mo) = true /\ BackingAlgebra.covered (vm_noaccess (m_vmmaps mo)) (bv_unsigned a) = false.
(* [comment removed for export] *)
Definition maps_zbound (mo : Model) : Prop :=
  Z.of_nat (length (vm_maps (m_vmmaps mo))) <= Z.of_nat (length (List.filter vpos (vm_maps (m_vmmaps mo)))) + 1.
Definition artm_sys (Σ : rtsA) (mo : Model) : Prop :=
  BackingAlgebra.model_ivs_wf mo /\ lazy_in_maps_A mo /\ ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo))
  /\ bv_unsigned (vm_init_sp (m_vmmaps mo)) = l_sp0 (lay Σ) /\ confined0 Σ mo /\ shadow_lazy mo /\ maps_zbound mo
  (* [comment removed for export] *)
  /\ NodesA_madv.noaccess_pos mo.

(* [comment removed for export] *)
Definition ARTM_A (Σ : rtsA) (mo : Model) : Prop :=
  Permutation (List.filter vpos (vm_maps (m_vmmaps mo))) (rt_maps Σ) /\ vm_reserved (m_vmmaps mo) = segments_reserved ctbsegs
  /\ vm_limit (m_vmmaps mo) = VMLIMIT /\ eager_used mo <= E0_MAX + rt_eager Σ /\ artm_sys Σ mo.

Definition RTA : rt_sig := mkRTS rtsA ART_A ARTM_A rtA_live rtA_frames rtA_allow rtA_sp0 rtA_credit.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma vis_premise_filter : forall (l : list (word * word)) (x : Z),
  (forall e, In e (List.filter vpos l) -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
  forall e, In e l -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e))).
Proof.
  intros l x H e He. destruct (vpos e) eqn:Ev.
  - exact (H e (proj2 (List.filter_In _ _ _) (conj He Ev))).
  - unfold vpos in Ev. apply Z.ltb_ge in Ev. pose proof (bv_unsigned_in_range _ (snd e)) as Hr.
    replace (bv_unsigned (snd e)) with 0 by (unfold bv_modulus in Hr; lia). rewrite Z.add_0_r. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
