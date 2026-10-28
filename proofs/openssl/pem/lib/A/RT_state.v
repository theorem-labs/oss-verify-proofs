(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_depot_defs R_fs_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition VMLIMIT : Z := 0x8000000000.
(* [comment removed for export] *)
Definition kUMap : Z := 0x40000.
Definition kFaCap : Z := 0x20000000.
Definition kUserCap : Z := 0xE0000000.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition QMAX_G : Z := 0x10000000.
Definition QMAX_L : Z := 0x100000.
(* [comment removed for export] *)
Definition SEC_MAX : Z := 16384.
(* [comment removed for export] *)
Definition CREDIT0 : Z := 2 ^ 37.
Definition E0_MAX : Z := 2 ^ 26.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record layoutA : Type := mkLayoutA {
  l_sp0 : Z;                 (* [comment removed for export] *)
  l_top : Z;                 (* [comment removed for export] *)
  l_PRB : Z;                 (* [comment removed for export] *)
  l_SB : Z;                  (* [comment removed for export] *)
  l_PAB : Z;                 (* [comment removed for export] *)
  l_T : Z;                   (* [comment removed for export] *)
  l_TCX : Z;                 (* [comment removed for export] *)
  l_DTV : Z;                 (* [comment removed for export] *)
  l_FSB : Z;                 (* [comment removed for export] *)
  l_DNB : Z;                 (* [comment removed for export] *)
  l_SSB : Z;                 (* [comment removed for export] *)
  l_f0 : Z;                  (* [comment removed for export] *)
  l_tid : Z;                 (* [comment removed for export] *)
  l_maps0 : list (word * word);   (* [comment removed for export] *)
  l_al0 : list (Z * Z);           (* [comment removed for export] *)
  l_cg : cgraph                   (* [comment removed for export] *)
}.

Definition l_ACEIL (L : layoutA) : Z := l_sp0 L - STACK_WIN.   (* [comment removed for export] *)
Definition l_RIS (L : layoutA) : Z := l_SB L + 2 ^ 37.

(* [comment removed for export] *)
Definition grant_ok (L : layoutA) (b n : Z) : Prop :=
  0 < b /\ b mod 4096 = 0 /\ b + n <= l_ACEIL L
  /\ (b + n <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= b)
  /\ (b + n <= 0x10000 \/ SEGTOP_A <= b).

Definition apart (b1 n1 b2 n2 : Z) : Prop := b1 + n1 <= b2 \/ b2 + n2 <= b1.

(* [comment removed for export] *)
Definition startup_grants (L : layoutA) : list (Z * Z) :=
  [ (l_PRB L, 0x2000011000); (l_PAB L, 0x800000); (l_T L, 4096); (l_TCX L, 0x10000); (l_DTV L, 4096); (l_FSB L, 0xb09000);
    (l_DNB L, 0x100000); (l_SSB L, 0x800000) ].

Definition pairwise_apart (gs : list (Z * Z)) : Prop :=
  forall i j g1 g2, (i < j)%nat -> nth_error gs i = Some g1 -> nth_error gs j = Some g2 -> apart (fst g1) (snd g1) (fst g2) (snd g2).

(* [comment removed for export] *)
Definition shadow_res : list (Z * Z) := [(0x7fff7000, 0x10000000); (0x8fff7000, 0x20000000000); (0x2008fff7000, 0xdfff0001000)].
(* [comment removed for export] *)
Definition vpos (e : word * word) : bool := Z.ltb 0 (bv_unsigned (snd e)).
Definition maps0_ok (L : layoutA) : Prop :=
  Forall (fun g => In (Z_to_bv 64 (fst g), Z_to_bv 64 (snd g)) (l_maps0 L)) (startup_grants L ++ shadow_res)
  /\ Z.of_nat (length (l_maps0 L)) <= 64 /\ live_bytes (l_maps0 L) <= 2 ^ 45
  /\ Forall (fun e => 0 < bv_unsigned (snd e)) (l_maps0 L).

(* [comment removed for export] *)
Definition layout_ok (L : layoutA) : Prop :=
  sp_window_lo <= l_sp0 L <= sp_window_hi /\ l_sp0 L mod 16 = 0
  /\ l_sp0 L - 0xa0 <= l_top L < l_sp0 L - 0xa0 + 4096 /\ l_top L mod 4096 = 0
  /\ grant_ok L (l_PRB L) 0x2000011000 /\ l_SB L mod 2 ^ 16 = 0 /\ l_PRB L <= l_SB L <= l_PRB L + 2 ^ 16
  /\ grant_ok L (l_PAB L) 0x800000 /\ grant_ok L (l_T L) 4096 /\ grant_ok L (l_TCX L) 0x10000
  /\ grant_ok L (l_DTV L) 4096 /\ grant_ok L (l_FSB L) 0xb09000 /\ grant_ok L (l_DNB L) 0x100000
  /\ grant_ok L (l_SSB L) 0x800000
  /\ apart (l_PRB L) 0x2000011000 (l_PAB L) 0x800000 /\ apart (l_PRB L) 0x2000011000 (l_T L) 4096
  /\ apart (l_PRB L) 0x2000011000 (l_TCX L) 0x10000 /\ apart (l_PRB L) 0x2000011000 (l_FSB L) 0xb09000
  /\ apart (l_PRB L) 0x2000011000 (l_DNB L) 0x100000 /\ apart (l_PRB L) 0x2000011000 (l_SSB L) 0x800000
  /\ apart (l_T L) 4096 (l_TCX L) 0x10000 /\ apart (l_T L) 4096 (l_FSB L) 0xb09000
  /\ apart (l_TCX L) 0x10000 (l_FSB L) 0xb09000 /\ apart (l_PAB L) 0x800000 (l_FSB L) 0xb09000
  /\ (l_f0 L = 2 \/ l_f0 L = 3) /\ 1 <= l_tid L < 2 ^ 31
  /\ A_wf (l_al0 L) /\ A_bytes (l_al0 L) <= 2 ^ 36
  /\ apart (l_DNB L) 0x100000 (l_SSB L) 0x800000
  /\ maps0_ok L          (* [comment removed for export] *)
  /\ pairwise_apart (startup_grants L).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive ckst : Type :=
| CkIdle                     (* [comment removed for export] *)
| CkAlloc (n : Z)            (* [comment removed for export] *)
| CkQuar (n : Z)             (* [comment removed for export] *)
| CkBatch.                   (* [comment removed for export] *)

Record regst : Type := mkReg {
  r_muser : Z;               (* [comment removed for export] *)
  r_mfa : Z;                 (* [comment removed for export] *)
  r_st : list ckst;          (* [comment removed for export] *)
  r_fl : list Z              (* [comment removed for export] *)
}.
Definition reg0 : regst := mkReg 0 0 [] [].

(* [comment removed for export] *)
Record secst : Type := mkSec { s_mb : Z; s_n : Z; s_quar : bool }.
(* [comment removed for export] *)
Definition pg_up (x : Z) : Z := ((x + 4095) / 4096) * 4096.
Definition pg_dn (x : Z) : Z := (x / 4096) * 4096.
Definition smsz (n : Z) : Z := pg_up (needed n + rz_size n) + 4096.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition batch : Type := (Z * list (Z * Z))%type.
Definition qn (b : batch) : Z := fold_right (fun e acc => snd e + acc) 0 (snd b).
Definition qsum (bs : list batch) : Z := fold_right (fun b acc => qn b + acc) 0 bs.
Definition qbytes (bs : list batch) : Z := qsum bs + 8192 * Z.of_nat (length bs).

(* [comment removed for export] *)
Record fsst : Type := mkFs { fss_hint : Z; fss_flags : list Z }.
Definition fs0_init (c : Z) : fsst := mkFs 0 (repeat 0 (Z.to_nat (NF c))).

(* [comment removed for export] *)
Definition PC_MALLOC : Z := 0x1c328c.     (* [comment removed for export] *)
Definition PC_FREE : Z := 0x1c312c.       (* [comment removed for export] *)
Definition PC_REALLOC : Z := 0x1c3760.    (* [comment removed for export] *)
Definition PC_MEMALIGN : Z := 0x1c3a08.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALLOC_EPS : list (Z * Z) :=
  [(e_malloc, PC_MALLOC); (e_free, PC_FREE); (e_realloc, PC_REALLOC); (e_posix_memalign, PC_MEMALIGN)].
(* [comment removed for export] *)
Definition N_TR : Z := 32000.
(* [comment removed for export] *)
Definition T_MAIN (cg : cgraph) : list (list Z) := cg_traces cg ALLOC_EPS ALLOC_RAS.
Definition DEP_BK (cg : cgraph) (h1 : Z) : list Z := bkt h1 :: map (fun tr => bkt (depot_hash tr)) (T_MAIN cg).

Record rtsA : Type := mkRtsA {
  lay : layoutA;
  pr : Z -> regst;           (* [comment removed for export] *)
  ca : Z -> list Z;          (* [comment removed for export] *)
  ca_init : bool;            (* [comment removed for export] *)
  sec : list secst;          (* [comment removed for export] *)
  sec_nres : Z;              (* [comment removed for export] *)
  aw : list (Z * Z);         (* [comment removed for export] *)
  ql : list batch;           (* [comment removed for export] *)
  qg : list batch;           (* [comment removed for export] *)
  dep : depot;
  fs0 : fsst; fs2 : fsst; fs1 : fsst;
  ia_init : bool;            (* [comment removed for export] *)
  credit : Z;                (* [comment removed for export] *)
  live : list (Z * Z);       (* [comment removed for export] *)
  frames : list (Z * nat)    (* [comment removed for export] *)
}.

Definition rtA_live (Σ : rtsA) : list (Z * Z) := live Σ.
Definition rtA_frames (Σ : rtsA) : list (Z * nat) := frames Σ.
Definition rtA_sp0 (Σ : rtsA) : Z := l_sp0 (lay Σ).
Definition rtA_credit (Σ : rtsA) : Z := credit Σ.

(* [comment removed for export] *)
Definition allow_main (L : layoutA) : list (Z * Z) :=
  [ (pg_dn (shad 0x10000), pg_up (shad SEGTOP_A));
    (pg_dn (shad (l_SB L)), pg_up (shad (l_SB L + 2 ^ 37)));
    (pg_dn (shad (l_FSB L)), pg_up (shad (l_FSB L + 0xb09000)));
    (pg_dn (shad (l_ACEIL L)), pg_up (shad (2 ^ 47)));
    (l_SSB L, l_SSB L + 0x800000) ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rtA_allow (Σ : rtsA) : list (Z * Z) := aw Σ ++ l_al0 (lay Σ) ++ allow_main (lay Σ).

(* [comment removed for export] *)
Definition secmap (s : secst) : word * word := (Z_to_bv 64 (s_mb s), Z_to_bv 64 (smsz (s_n s))).
Definition rt_maps (Σ : rtsA) : list (word * word) := map secmap (rev (sec Σ)) ++ l_maps0 (lay Σ).

(* [comment removed for export] *)
Fixpoint sum_cls (f : Z -> Z) (k : nat) : Z :=
  match k with O => 0 | S k' => f (Z.of_nat k) + sum_cls f k' end.
Definition rt_eager (Σ : rtsA) : Z :=
  sum_cls (fun c => r_muser (pr Σ c) + r_mfa (pr Σ c)) 31
  + fold_right (fun s acc => smsz (s_n s) + acc) 0 (sec Σ) + 8 * sec_nres Σ.

(* [comment removed for export] *)
Definition p_abeg (SB c : Z) (i : nat) : Z := SB + c * 2 ^ 32 + Z.of_nat i * ClassSize c.
Definition p_ubeg (SB c : Z) (i : nat) (n : Z) : Z := p_abeg SB c i + rz_size n.
Definition s_ubeg (s : secst) : Z := s_mb s + 4096 + 2048.

(* [comment removed for export] *)
Definition count_st (f : ckst -> bool) (l : list ckst) : nat := length (filter f l).
Definition is_alloc (s : ckst) : bool := match s with CkAlloc _ => true | _ => false end.
Definition is_quar (s : ckst) : bool := match s with CkQuar _ => true | _ => false end.
Definition is_batch (s : ckst) : bool := match s with CkBatch => true | _ => false end.
Definition is_idle (s : ckst) : bool := match s with CkIdle => true | _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition reg_wf (c : Z) (r : regst) : Prop :=
  0 <= r_muser r <= kUserCap /\ r_muser r mod kUMap = 0
  /\ ClassSize c * Z.of_nat (length (r_st r)) <= r_muser r
  /\ r_muser r < ClassSize c * Z.of_nat (length (r_st r)) + ClassSize c     (* [comment removed for export] *)
  /\ 0 <= r_mfa r <= kFaCap /\ r_mfa r mod kUMap = 0 /\ 4 * Z.of_nat (length (r_fl r)) <= r_mfa r
  /\ NoDup (r_fl r)
  /\ Forall (fun i => 0 <= i < Z.of_nat (length (r_st r)) /\ nth_error (r_st r) (Z.to_nat i) = Some CkIdle) (r_fl r)
  (* [comment removed for export] *)
  /\ Forall (fun st => match st with CkAlloc n | CkQuar n => 1 <= n /\ rz_size n + n <= ClassSize c /\ c = ClassID (needed n)
                                   | _ => True end) (r_st r)
  (* [comment removed for export] *)
  /\ ClassSize c * Z.of_nat (length (r_st r)) <= 2 ^ 31.

Definition regs_wf (Σ : rtsA) : Prop :=
  (forall c, 1 <= c <= 31 -> reg_wf c (pr Σ c)) /\ (forall c, (c < 1 \/ 31 < c) -> pr Σ c = reg0)
  (* [comment removed for export] *)
  /\ (forall c, 1 <= c <= 31 ->
        Z.of_nat (length (ca Σ c)) <= MaxCount c /\ NoDup (ca Σ c ++ r_fl (pr Σ c))
        /\ Forall (fun i => 0 <= i < Z.of_nat (length (r_st (pr Σ c)))
                            /\ nth_error (r_st (pr Σ c)) (Z.to_nat i) = Some CkIdle) (ca Σ c))
  /\ (ca_init Σ = false -> forall c, ca Σ c = [])
  (* [comment removed for export] *)
  /\ (forall c i, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some CkIdle -> In (Z.of_nat i) (ca Σ c ++ r_fl (pr Σ c)))
  (* [comment removed for export] *)
  /\ (ca_init Σ = false -> forall c, r_st (pr Σ c) = []).

(* [comment removed for export] *)
Definition live_wf (Σ : rtsA) : Prop :=
  Z.of_nat (length (live Σ)) <= LIVE_MAX /\ NoDup (map fst (live Σ))
  /\ (forall p n, In (p, n) (live Σ) ->
        (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg (l_SB (lay Σ)) c i n)
        \/ (exists s, In s (sec Σ) /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s))
  /\ (forall c i n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
        In (p_ubeg (l_SB (lay Σ)) c i n, n) (live Σ))
  /\ (forall s, In s (sec Σ) -> s_quar s = false -> In (s_ubeg s, s_n s) (live Σ)).

(* [comment removed for export] *)
Definition sec_wf (Σ : rtsA) : Prop :=
  Z.of_nat (length (sec Σ)) <= SEC_MAX /\ (sec_nres Σ = 0 \/ sec_nres Σ = 0x4000)
  /\ (sec Σ <> [] -> sec_nres Σ = 0x4000)
  /\ Forall (fun s => 64513 <= s_n s <= 0x8000000 /\ grant_ok (lay Σ) (s_mb s) (smsz (s_n s))
                     /\ apart (s_mb s) (smsz (s_n s)) (l_PRB (lay Σ)) 0x2000011000
                     /\ apart (s_mb s) (smsz (s_n s)) (l_FSB (lay Σ)) 0xb09000
                     /\ Forall (fun g => apart (s_mb s) (smsz (s_n s)) (fst g) (snd g)) (startup_grants (lay Σ))) (sec Σ)
  /\ (forall k1 k2 s1 s2, nth_error (sec Σ) k1 = Some s1 -> nth_error (sec Σ) k2 = Some s2 -> k1 <> k2 ->
        apart (s_mb s1) (smsz (s_n s1)) (s_mb s2) (smsz (s_n s2)))
  (* [comment removed for export] *)
  /\ Forall (fun s => In (pg_dn (shad (s_mb s)), pg_up (shad (s_mb s + smsz (s_n s)))) (aw Σ)) (sec Σ).

(* [comment removed for export] *)
Definition qents (Σ : rtsA) : list (Z * Z) := flat_map snd (ql Σ ++ qg Σ).

(* [comment removed for export] *)
Definition qent_ok (Σ : rtsA) (e : Z * Z) : Prop :=
  (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkQuar (snd e))
               /\ fst e = p_abeg (l_SB (lay Σ)) c i + rz_size (snd e) - 16)
  \/ (exists s, In s (sec Σ) /\ s_quar s = true /\ s_n s = snd e /\ fst e = s_mb s + 6128).

(* [comment removed for export] *)
Definition quar_wf (Σ : rtsA) : Prop :=
  qbytes (ql Σ) <= QMAX_L + 0x10000 /\ qbytes (qg Σ) <= QMAX_G + 0x10000
  (* [comment removed for export] *)
  /\ Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ)
  /\ NoDup (map fst (ql Σ ++ qg Σ))
  (* [comment removed for export] *)
  /\ Forall (fun b => (length (snd b) <= 1021)%nat) (ql Σ ++ qg Σ)
  /\ Forall (qent_ok Σ) (qents Σ) /\ NoDup (map fst (qents Σ))
  (* [comment removed for export] *)
  /\ (forall c i, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some CkBatch ->
        c = 24 /\ In (p_abeg (l_SB (lay Σ)) 24 i) (map fst (ql Σ ++ qg Σ))).

(* [comment removed for export] *)
Definition fs_cls_wf (c : Z) (f : fsst) : Prop :=
  flags_ok c (fss_flags f) /\ 0 <= fss_hint f < 2 ^ 61 /\ Z.of_nat (nbusy (fss_flags f)) <= 16.
Definition fs_of (Σ : rtsA) (k : nat) : fsst := match k with 0%nat => fs0 Σ | 2%nat => fs2 Σ | _ => fs1 Σ end.
Definition fs_wf (Σ : rtsA) : Prop :=
  fs_cls_wf 0 (fs0 Σ) /\ fs_cls_wf 2 (fs2 Σ) /\ fs_cls_wf 1 (fs1 Σ)
  /\ Forall (fun fk => (snd fk = 0%nat \/ snd fk = 2%nat \/ snd fk = 1%nat)
                      /\ exists p, 0 <= p < NF (Z.of_nat (snd fk)) /\ fst fk = frame_addr (l_FSB (lay Σ)) (Z.of_nat (snd fk)) p
                                  /\ nth (Z.to_nat p) (fss_flags (fs_of Σ (snd fk))) 0 = 1) (frames Σ)
  /\ NoDup (frames Σ) /\ Z.of_nat (length (frames Σ)) <= 16
  (* [comment removed for export] *)
  /\ (forall k, (k = 0 \/ k = 2 \/ k = 1)%nat ->
        Z.of_nat (nbusy (fss_flags (fs_of Σ k))) = Z.of_nat (length (List.filter (fun fk => Nat.eqb (snd fk) k) (frames Σ))))
  /\ (forall k, (k = 0 \/ k = 2 \/ k = 1)%nat -> fss_hint (fs_of Σ k) <= 2 ^ 14 * (CREDIT0 - credit Σ)).

(* [comment removed for export] *)
Definition secsum (Σ : rtsA) : Z := fold_right (fun s acc => smsz (s_n s) + acc) 0 (sec Σ).

(* [comment removed for export] *)
Definition budget_wf (Σ : rtsA) : Prop :=
  0 <= credit Σ /\ A_wf (aw Σ) /\ A_bytes (aw Σ) + credit Σ <= CREDIT0 /\ rt_eager Σ <= 2 ^ 38
  /\ secsum Σ <= CREDIT0 - credit Σ.

(* [comment removed for export] *)
Definition dep_inv (cg : cgraph) (D : depot) : Prop :=
  List.NoDup (d_hs D) /\ (forall h, In h (d_hs D) -> h = hash_of (d_hs D) 1 \/ In h (map depot_hash (T_MAIN cg)))
  /\ 1 <= d_n D /\ d_tot D <= 31 * d_n D /\ cg_wf cg ALLOC_EPS ALLOC_RAS N_TR.

(* [comment removed for export] *)
Definition rt_count (Σ : rtsA) : Prop :=
  (forall c i n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
     In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n) (qents Σ))
  /\ (forall s, In s (sec Σ) -> s_quar s = true -> In (s_mb s + 6128, s_n s) (qents Σ)).

(* [comment removed for export] *)
Definition rt_wf0 (Σ : rtsA) : Prop :=
  layout_ok (lay Σ) /\ regs_wf Σ /\ live_wf Σ /\ sec_wf Σ /\ quar_wf Σ /\ fs_wf Σ /\ budget_wf Σ
  /\ depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ))
  /\ d_n (dep Σ) + 2 < 2 ^ 16 /\ d_tot (dep Σ) + 255 < 2 ^ 20 /\ dep_inv (l_cg (lay Σ)) (dep Σ).

Definition rt_wf (Σ : rtsA) : Prop :=
  layout_ok (lay Σ) /\ regs_wf Σ /\ live_wf Σ /\ sec_wf Σ /\ quar_wf Σ /\ fs_wf Σ /\ budget_wf Σ
  /\ depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ))
  /\ d_n (dep Σ) + 2 < 2 ^ 16 /\ d_tot (dep Σ) + 255 < 2 ^ 20 /\ dep_inv (l_cg (lay Σ)) (dep Σ) /\ rt_count Σ.

Lemma rt_wf_split : forall Σ, rt_wf Σ <-> rt_wf0 Σ /\ rt_count Σ.
Proof. intros Σ. unfold rt_wf, rt_wf0. tauto. Qed.
