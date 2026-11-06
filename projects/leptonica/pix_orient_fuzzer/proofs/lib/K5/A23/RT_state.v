(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import R_depot_defs R_fs_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require RT_traces.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_state () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC35stdpp4base6ElemOfC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:fold_rightI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbc69OSSVerify5KrLib2K53A238RT_state5batchC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00c69OSSVerify5KrLib2K53A238RT_state3layC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state9layout_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state7regs_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state7live_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state6sec_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state7quar_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state5fs_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state9budget_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state3depC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01c69OSSVerify5KrLib2K53A238RT_state7dep_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state8rt_countC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indc69OSSVerify5KrLib2K53A238RT_state5rt_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state6rt_wf0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffc69OSSVerify5KrLib2K53A238RT_state5l_DNBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state5l_SSBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_depot_defs8depot_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_depot_defs3d_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53A23<R_depot_defs5d_totC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2K53A238RT_state4rtsA00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
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
(* [comment removed for export] *)
Definition SEC_MAX : Z := 14336.
(* [comment removed for export] *)
Definition CARVE_MAX : Z := 0xD8000000.
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
  l_al0 : list (Z * Z)            (* [comment removed for export] *)
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
Definition PC_MALLOC : Z := 0xcb240.     (* [comment removed for export] *)
Definition PC_FREE : Z := 0xcb0e0.       (* [comment removed for export] *)
Definition PC_STRDUP : Z := 0xad57c.     (* [comment removed for export] *)
Definition RA_STRNDUP : Z := 0xa72bc.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_MAIN : list (list Z) := RT_traces.T_MAIN.
Definition DEP_BK (h1 : Z) : list Z := bkt h1 :: map (fun tr => bkt (depot_hash tr)) T_MAIN.

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
  fs0 : fsst; fs2 : fsst; fs4 : fsst; fs1 : fsst;   (* [comment removed for export] *)
  fc3 : fsst; fc4 : fsst; fc7 : fsst;              (* [comment removed for export] *)
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
  /\ ClassSize c * Z.of_nat (length (r_st r)) <= 0xD8000000 (* [comment removed for export] *).

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
Definition fs_of (Σ : rtsA) (k : nat) : fsst := match k with 0%nat => fs0 Σ | 1%nat => fs2 Σ | 2%nat => fs1 Σ | 3%nat => fc3 Σ | 4%nat => fc4 Σ | 7%nat => fc7 Σ | _ => fs4 Σ end.
Definition fs_wf (Σ : rtsA) : Prop :=
  fs_cls_wf 0 (fs0 Σ) /\ fs_cls_wf 1 (fs2 Σ) /\ (fs_cls_wf 6 (fs4 Σ) /\ fs_cls_wf 2 (fs1 Σ) /\ fs_cls_wf 3 (fc3 Σ) /\ fs_cls_wf 4 (fc4 Σ) /\ fs_cls_wf 7 (fc7 Σ))
  /\ Forall (fun fk => (snd fk = 0%nat \/ snd fk = 1%nat \/ snd fk = 6%nat \/ snd fk = 2%nat \/ snd fk = 3%nat \/ snd fk = 4%nat \/ snd fk = 7%nat)
                      /\ exists p, 0 <= p < NF (Z.of_nat (snd fk)) /\ fst fk = frame_addr (l_FSB (lay Σ)) (Z.of_nat (snd fk)) p
                                  /\ nth (Z.to_nat p) (fss_flags (fs_of Σ (snd fk))) 0 = 1) (frames Σ)
  /\ NoDup (frames Σ) /\ Z.of_nat (length (frames Σ)) <= 16
  (* [comment removed for export] *)
  /\ (forall k, (k = 0 \/ k = 1 \/ k = 6 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 7)%nat ->
        Z.of_nat (nbusy (fss_flags (fs_of Σ k))) = Z.of_nat (length (List.filter (fun fk => Nat.eqb (snd fk) k) (frames Σ))))
  /\ (forall k, (k = 0 \/ k = 1 \/ k = 6 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 7)%nat -> fss_hint (fs_of Σ k) <= 2 ^ 14 * (CREDIT0 - credit Σ)).

(* [comment removed for export] *)
Definition secsum (Σ : rtsA) : Z := fold_right (fun s acc => smsz (s_n s) + acc) 0 (sec Σ).

(* [comment removed for export] *)
Definition budget_wf (Σ : rtsA) : Prop :=
  0 <= credit Σ /\ A_wf (aw Σ) /\ A_bytes (aw Σ) + credit Σ <= CREDIT0 /\ rt_eager Σ <= 2 ^ 38
  /\ secsum Σ <= CREDIT0 - credit Σ.

(* [comment removed for export] *)
Definition dep_inv (D : depot) : Prop :=
  List.NoDup (d_hs D) /\ (forall h, In h (d_hs D) -> h = hash_of (d_hs D) 1 \/ In h (map depot_hash T_MAIN))
  /\ 1 <= d_n D /\ d_tot D <= 10 * d_n D.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_count (Σ : rtsA) : Prop :=
  (forall c i n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
     In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n) (qents Σ))
  /\ (forall s, In s (sec Σ) -> s_quar s = true -> In (s_mb s + 6128, s_n s) (qents Σ)).

(* [comment removed for export] *)
Definition rt_wf0 (Σ : rtsA) : Prop :=
  layout_ok (lay Σ) /\ regs_wf Σ /\ live_wf Σ /\ sec_wf Σ /\ quar_wf Σ /\ fs_wf Σ /\ budget_wf Σ
  /\ depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ))
  /\ d_n (dep Σ) + 2 < 2 ^ 16 /\ d_tot (dep Σ) + 255 < 2 ^ 20 /\ dep_inv (dep Σ).

Definition rt_wf (Σ : rtsA) : Prop :=
  layout_ok (lay Σ) /\ regs_wf Σ /\ live_wf Σ /\ sec_wf Σ /\ quar_wf Σ /\ fs_wf Σ /\ budget_wf Σ
  /\ depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ))
  /\ d_n (dep Σ) + 2 < 2 ^ 16 /\ d_tot (dep Σ) + 255 < 2 ^ 20 /\ dep_inv (dep Σ) /\ rt_count Σ.

Lemma rt_wf_split : forall Σ, rt_wf Σ <-> rt_wf0 Σ /\ rt_count Σ.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_state ()) [] "h01Hh12H2h22H3h32H4h42H5h52H6h62H7h72H8h82H9h92H0h:2H1h;3H10h<3H11h=2Σp%0p%1p;1p;2p;4p;5p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cp4p710p8P0p1001DR1p4p710p8P0P1p4p7210p8P0p1001ap4p710R1p8P0p1002AR2p4p710R3p8P0P2p4p7210R2p8P0p1002UR4p4p710p8P0P4p4p7210p8P0p10032p4p7210R4p8P0p1003Qp4p710R5p8P0p1003mp4p710p8p1004Ip4p70R0P1p8P0p1005Cp4p710p8P0P4p8p1005`p4p710R4P3p8P4P2p8P4P5p8g0065j17Tg006mj1?Tg007kj1>Tg008gj1=Tg009cj1<Tg00:^j1;Tg00;Zj1:Tg00<Tj18Tg00=Rj12Tg00>Jj1HTg00>oj1LTg00?Mj2MTg00?jj1FTg00@Oj13Tg00AKj19Tg00BHj20Tg00Bcj4JTg00C>j5ITg00C[j1XTg00DUj1WTg00EPj2VTg00Eij1UTg00Fcj1TTg00G]j1QTg00HYj4RTg00IZj1STg00JVj2PTg00K3j2OTg00KOj1ZTf3R5f2R4#Uf1R2#Tf0R3#QCRp=6%S4/P2/O3p=5%Z4/P2/O3p=41023,04,05p=@f4R01023,04,05'0p=1f6R1f5R61023,04,05,00'0'0p=B1023,04,05,00,06p=E1042/03p=Y%93,02p=K1023,04p=GP1P6P0P5P4P2P3CJCJp=Af7R7P11005,06/04P2P3DIp=CP6P01054P2P3DIp=NP7P11054,00,06P2P3DIp=Dg00LM%73R8#?R9%>3R:%=3R;%<3R<%;3R=%:3R>%83R?%23R@P8P8P8C6R8g00MHRA#HRB#LRC%HB#H#H#L,MCRD55@RE%FA#F#F#F#F#F#F#LRA%FB#H#H#L,MCRB54@RF%3@R@%93RGC@D1D1RH%72RI#?RJ%>2RK%=2RL%<2RM%;2RN%:2RO%82RP%22RQPIPIPIC6RIA5QCDRRA4QABRS%3QRQFBD1RT%92RU'0RV[P:P;P<P=P>P?P8PEPFP@EED1=Y9GR9PKPLPMPNPOPPPIPRPSPQPUFBD1RQ,0JS00[PJPQPV%>4%=4%<4%;4%:4%84%24RV%74RQPQPQC6A5VCDA4VAB%3V%94R4FBD1%>5RV%=5RQ%<5RS%;5RR%:5RI%85RP%25RO%75RNPNPNC6RMA5OCDRLA4OABRK%3ORO%95R@EED1RF%?NRNPVPQPSPRPIPPPMPLPKPOEED1S01'0P@%=0S02%<0S03%;0S04%:0S05%80S06%20R@%70ROPOPOC6S07A5@CDS08A4@ABS09%3@S0:/K0D1D1%=6R@%<6RO%;6RK%:6RL%86RM%26RP%76RIPIPIC6RRA5PCDRSA4PABRQ%3PRP%96RED1D1S0;%?IS0<%>6RIP@POPKPLPMPRPSPQPPD1D1S0=PE%<1S0>%;1S0?%:1S0@%81S0A%21RE%71RPPPPPC6S0BA5ECDS0CA4EABS0D%3ES0E%91D1D1%<7RE%;7RP%:7RQ%87RS%27RR%77RMPMPMC6RLA5RCDRKA4RABRO%3RRR%97R8C@D1R?%?MS0F%>7S0G%=7RMPEPPPQPSPLPKPOPRC@D1S0H'0P8f8R8#;S0I%:8S0J%88S0K%28RR%78ROPOPOC6S0LA5RCDS0MA4RABS0N%3RS0O/K8FBf9RR#;RO%:RRK%8RRL%2RRS%7RRQPQPQC6RPA5SCDR>A4SABR=%3SRS%9RR<FBR;%?QS0P%>RS0Q%=RS0R%<RRQPOPKPLPPP>P=PSFBS0S3GP<f:R<#:S0T%8<S0U%2<RS%7<R=P=P=C6S0VA5SCDS0WA4SABS0X%3SS0Y%9<FBf;RS#:R=%8SR>%2SRP%7SRLPLPLC6RKA5PCDR:A4PABRW%3PRP%9SRXEES0Z%?LS0[%>SS0\%=SS0]%<SS0^%;SRLP=P>PKP:PWPPEES0_C@PXf<RX#8S0`%2XRP%7XRWPWPWC6S0aA5PCDS0bA4PABS0c%3PS0d/KXD1f=RP#8RW%2PR:%7PRKPKPKC6R>A5:CDRYA4:ABRZ%3:R:%9PR[D1S0e%?KS0f%>PS0g%=PS0h%<PS0i%;PS0j%:PRKPWP>PYPZP:D1S0kD1P[f>R[#2R:%7[RZPZPZC6S0lA5:CDS0mA4:ABS0n%3:S0o%9[D1f?R:#2RZ%7:RYPYPYC6R>A5ZCDR\A4ZABR]%3ZRZ%9:R^C@S0p%?YS0q%>:S0r%=:S0s%<:S0t%;:S0u%::S0v%8:RYP>P\P]PZC@S0wEEP^f@R^#2RZ?5CDS0xA4ZABS0y%3ZS0z/K^3GfAR]#2R\?5CDR_A4\ABR`%3\Ra%9]Rb3GS0{%7]Rc#?S0|%>]S0}%=]S0~%<]S10%;]S11%:]S12%8]S13P\PcPcPcC6RcAG_`aS14FBPbfBRb#2Ra?4ABR`%3aR\%9b3GfCRb#2Rd?4ABRe%3dRf%9bRg'0S15%7bRh#?S16%>bS17%=bS18%<bS19%;bS1:%:bS1;%8bS1<PdPhPhPhC6S1=A5dCDRd10efS1>C@D1PgfDRg#2Rf#3Rh/KgfERi#2Rj#3Rk%9iRl%7iRm#?S1?%>iS1@%=iS1A%<iS1B%;iS1C%:iS1D%8iS1EPjPmPmPmC6S1FA5jCDS1GA4jABRjPkD1D1PlfFRm#9fGRn#7Ro#?Rp%>nRq%=nRr%<nRs%;nRt%:nRu%8nRv%2nRwPoPoPoC6RoA5wCDRxA4wABRy%3wRw'0S1H'0S1I'0S1J'0S1K'0Rz'0R{'0R|'0R}'0R~'0%9nRnPpP~PiPqP}PbPrP|P]PsP{P:PtPzPPPuQ1KPSPvQ1JPRPoQ1IP7PxQ1HP6PyPwP5P2FAFAFAFAFAP3CJW<X8kP3GCW;X7eP3GCW8X6_P3GCW7X5>P3GCW6X4WP3GCW5X3=P3GCW4X2OP3GCW3X1EP3GCW2X:@P3GCW1X0VP3ENW:X9JP3DIX0HPTPUQ00PNQ01PN10VF%>0Q02Q03Q04Q05Q06Q07Q08Q09Q0:EED1PIQ0=Q0<PIP@Q0;%=1Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0ED1D1PMQ0HQ0FQ0GPM10E?%<8Q0IQ0JQ0KQ0LQ0MQ0NQ0OC@D1PQQ0SQ0PQ0QQ0RAGQO;%;<Q0TQ0UQ0VQ0WQ0XQ0YFBPLQ0_Q0[Q0\Q0]Q0^PLP=Q0ZC@%:XQ0`Q0aQ0bQ0cQ0dEEPKQ0kQ0fQ0gQ0hQ0iQ0jPKPWQ0eD1%8[Q0lQ0mQ0nQ0oD1PYQ0wQ0qQ0rQ0sQ0tQ0uQ0vPYP>Q0pEEPZ%7^R^P^P^C6Q0xQ0yQ0zC@PcQ14Q0|Q0}Q0~Q10Q11Q12Q13PcP_Q0{FBA5aCD?G`\PdQ1>Q16Q17Q18Q19Q1:Q1;Q1<Q1=PdPeQ15C@D1A4fAB/0hPjPkQ1?Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1GPjPkPlD1D1%2m#3Pp10wnRp,0yRm,0xRl,0oRk,0vRh,0uRf,0tRB,0sRA,0rRe,0qPbPqPeP]PrPAP:PsPBPPPtPfPSPuPhPRPvPkP7PoPlP6PxPmP5PyPpP2PwPnP3PgCJFAFAFAFAFAW<X8jP3GDW;X7dP3GDW8X6cP3GDW7X5YP3GDW6X4KP3GDW5X3LP3GDW4X2QP3GDW3X1MP3GDW2X9IP3GDW1X0NP2ENX:4X9TP3DIX09CJ%X3%W3/0G'VeW=o"). Qed.
