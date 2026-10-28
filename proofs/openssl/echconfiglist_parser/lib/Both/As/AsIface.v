(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMALLOC_ICPT : Z := 0x1bf354.  (* [comment removed for export] *)
Definition AFREE_ICPT   : Z := 0x1bf184.  (* [comment removed for export] *)
Definition AMALLOC_STUB : Z := 0x1bf174.  (* [comment removed for export] *)
Definition AFREE_STUB   : Z := 0x1bf170.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFS_MALLOC_1 : Z := 0x1a26c0.   (* [comment removed for export] *)
Definition AFS_MALLOC_4 : Z := 0x1a2b98.   (* [comment removed for export] *)
Definition ASET_SHADOW_F5 : Z := 0x1c14b4. (* [comment removed for export] *)
Definition ASET_SHADOW_00 : Z := 0x1c13ac. (* [comment removed for export] *)
Definition AASAN_MEMCPY  : Z := 0x1bdab0.
Definition AASAN_MEMSET  : Z := 0x1bdf4c.
Definition AASAN_MEMMOVE : Z := 0x1be18c.
(* [comment removed for export] *)
Definition ASTRLEN_STUB  : Z := 0x1a86f8.  (* [comment removed for export] *)
Definition ASTRNCMP_STUB : Z := 0x1a8704.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMEMCPY_STUB  : Z := 0x1bdaac. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AREPORT_LOAD1 : Z := 0x1c5ab0.  Definition AREPORT_LOAD4 : Z := 0x1c5bf0.  Definition AREPORT_LOAD8 : Z := 0x1c5c90.
Definition AREPORT_STORE1 : Z := 0x1c5dd0. Definition AREPORT_STORE4 : Z := 0x1c5f10. Definition AREPORT_STORE8 : Z := 0x1c5fb0.
Definition AREPORT_N : Z := 0x1c60f0.      Definition AHANDLE_NO_RETURN : Z := 0x1c6aac.

(* [comment removed for export] *)
Definition APC0_MALLOC : Z := 0x1bf41c.
Definition APC0_FREE   : Z := 0x1bf2bc.

(* [comment removed for export] *)
Definition ATP    : Z := 0xbe1c90.
Definition AERRNO : Z := ATP - 0xa4.
(* [comment removed for export] *)
Definition ATLS_PRIV_SZ : Z := 0x14.
Definition ATLS_PRIV_LO : Z := ATP - 88.
Definition ATLS_PRIV_HI : Z := ATP + 0x30.
Definition ATSD0 : Z := 0xc03038.      (* [comment removed for export] *)
Definition ALIBC_PGSZ : Z := 0xc01f50. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 8192.   (* [comment removed for export] *)
Definition AFREE_STACK   : Z := 8192.   (* [comment removed for export] *)
Definition AFS_STACK     : Z := 1024.   (* [comment removed for export] *)
Definition AINTRIN_STACK : Z := 4096.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AFS_SIZE : Z := 0xb09000.            (* [comment removed for export] *)
Definition AFS_HDR  : Z := 0x9000.              (* [comment removed for export] *)
Definition AFS_FLAGS : Z := 0x1000.             (* [comment removed for export] *)
Definition fsz (k : Z) : Z := 64 * 2 ^ k.       (* [comment removed for export] *)
Definition fshn (k : Z) : Z := 8 * 2 ^ k.       (* [comment removed for export] *)
Definition AFS_MAXLIVE : nat := 1000.            (* [comment removed for export] *)

Definition mem := word -> option byte.
Definition bptr : Type := Z.                    (* [comment removed for export] *)
Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.
Definition in_block (LB : list block) (a : Z) : Prop := exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.
(* [comment removed for export] *)
Definition in_block_sh (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ sh (blk_addr b) <= a < sh (blk_addr b) + nsh (blk_size b).
Definition lb_bytes (LB : list block) : Z := fold_right (fun b acc => blk_size b + acc) 0 LB.

(* [comment removed for export] *)
Definition fframe : Type := (Z * Z * Z)%type.
Definition ff_class (f : fframe) : Z := fst (fst f).
Definition ff_addr (f : fframe) : Z := snd (fst f).
Definition ff_flag (f : fframe) : Z := snd f.
Fixpoint lf_remove (ff : Z) (LF : list fframe) : list fframe :=
  match LF with [] => [] | f :: LF' => if Z.eqb (ff_addr f) ff then LF' else f :: lf_remove ff LF' end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Record asr := {
  as_St       : Type ;                                         (* [comment removed for export] *)
  as_SR       : (config -> Prop) -> config -> Prop ;           (* [comment removed for export] *)
  as_VIS      : as_St -> machine_state -> machine_state ;      (* [comment removed for export] *)
  as_AKREL    : as_St -> config -> Prop ;                      (* [comment removed for export] *)
  as_MPRES    : Model -> Model -> Prop ;                       (* [comment removed for export] *)
  as_RHEAP    : as_St -> list block -> mem -> Prop ;           (* [comment removed for export] *)
  as_RFS      : list fframe -> mem -> Prop ;                   (* [comment removed for export] *)
  as_rauxv_ok : mem -> Z -> Prop ;                             (* [comment removed for export] *)
  as_lb_remove : bptr -> list block -> list block ;
  as_alloc_ok : as_St -> list block -> Z -> Prop ;             (* [comment removed for export] *)
  as_LIVE_MAX : Z ; as_LIVE_CNT_MAX : Z ;
  as_AL       : as_St -> Z ;                                   (* [comment removed for export] *)
  as_Cm       : Z -> Z ; as_Cf : Z -> Z ;                      (* [comment removed for export] *)
  as_chain    : mem -> Z -> list (Z * Z) -> Prop ;             (* [comment removed for export] *)
  as_TR       : list (list Z) ;                                (* [comment removed for export] *)
  as_FSB      : Z                                              (* [comment removed for export] *)
}.

Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Abbreviation SR := (as_SR H).  Abbreviation VIS := (as_VIS H).  Abbreviation AKREL := (as_AKREL H).  Abbreviation MPRES := (as_MPRES H).
  Abbreviation RHEAP := (as_RHEAP H).  Abbreviation RFS := (as_RFS H).  Abbreviation rauxv_ok := (as_rauxv_ok H).
  Abbreviation lb_remove := (as_lb_remove H).  Abbreviation alloc_ok := (as_alloc_ok H).
  Abbreviation AL := (as_AL H).  Abbreviation Cm := (as_Cm H).  Abbreviation Cf := (as_Cf H).
  Abbreviation CHAIN := (as_chain H).  Abbreviation TR := (as_TR H).  Abbreviation FSB := (as_FSB H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition aimg_client (a : Z) : Prop :=
    (0x571000 <= a < 0x5ea848) \/ (0x5ed1a0 <= a < 0x6a7220) \/ (0x6a7248 <= a < 0x6a7298)
    \/ (0xbccf50 <= a < 0xc03570).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition aimg_client_w (lo hi : Z) : Prop :=
    (0x5ea840 <= lo /\ hi <= 0x5ea848) \/ (0x5ed1a0 <= lo /\ hi <= 0x5edfa0) \/ (0x6a7248 <= lo /\ hi <= 0x6a7298)
    \/ (0xbccf50 <= lo /\ hi <= ATLS_PRIV_LO) \/ (ATLS_PRIV_HI <= lo /\ hi <= ALIBC_PGSZ) \/ (ALIBC_PGSZ + 8 <= lo /\ hi <= ATSD0)
    \/ (ATSD0 + 8 <= lo /\ hi <= 0xc03570).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition aclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
    SP <= a
    \/ aimg_client a
    \/ in_block LB a \/ in_block_sh LB a
    \/ (FSB <= a < FSB + AFS_SIZE) \/ (sh FSB <= a < sh (FSB + AFS_SIZE))
    \/ (sh aceil <= a < AHI_LO).

  Definition apres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
    forall a, 0 <= a < 2^64 -> aclient_addr LB SP a ->
      m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

  (* [comment removed for export] *)
  Definition aclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
    aceil <= fst iv
    \/ aimg_client_w (fst iv) (snd iv)
    \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
    \/ (exists b, In b LB /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b))
    \/ (FSB <= fst iv /\ snd iv <= FSB + AFS_SIZE) \/ (sh FSB <= fst iv /\ snd iv <= sh (FSB + AFS_SIZE))
    \/ (sh aceil <= fst iv /\ snd iv <= AHI_LO).

  (* [comment removed for export] *)
  Definition afs_write_ok (LF : list fframe) (iv : Z * Z) : Prop :=
    ((snd iv <= FSB \/ FSB + AFS_SIZE <= fst iv) /\ (snd iv <= ATLS_PRIV_LO \/ ATLS_PRIV_HI <= fst iv))
    \/ (exists f, In f LF /\ ff_addr f <= fst iv /\ snd iv <= ff_addr f + fsz (ff_class f)).

  (* [comment removed for export] *)
  Definition ablock_range (A n : Z) : Prop :=
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ AIMG_TOP <= A /\ A + n <= aceil /\ (A + n + 16 <= FSB \/ FSB + AFS_SIZE <= A - 16)
    /\ aapp A n.
  (* [comment removed for export] *)
  Definition aframe_range (k ff fp : Z) : Prop :=
    0 <= k <= 10 /\ FSB + AFS_HDR <= ff /\ ff + fsz k <= FSB + AFS_SIZE /\ ff mod (fsz k) = 0
    /\ FSB + AFS_FLAGS <= fp < FSB + AFS_HDR.
  Definition afsb_ok : Prop := AIMG_TOP <= FSB /\ FSB + AFS_SIZE <= aceil /\ FSB mod 4096 = 0 /\ aapp FSB AFS_SIZE.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition athr_cells (m : mem) : Prop :=
    exists (ctx T D : Z) (tb te : bv 64),
         rw_cells asegs m ATSD0 [C8 (wz ctx)]                 (* [comment removed for export] *)
      /\ rw_cells asegs m (ctx + 152) [C8 (wz T)]             (* [comment removed for export] *)
      /\ rw_cells asegs m (T + 48) [C8 tb; C8 te]             (* [comment removed for export] *)
      /\ rw_cells asegs m (ATP + 24) [C8 (wz D)]              (* [comment removed for export] *)
      /\ rw_cells asegs m (D + 24) [C8 (wz ATP)]              (* [comment removed for export] *)
      /\ 0 < ctx /\ ctx mod 8 = 0 /\ ctx + 160 <= aceil
      /\ 0 < T /\ T mod 8 = 0 /\ T + 64 <= aceil
      /\ 0 < D /\ D mod 8 = 0 /\ D + 32 <= aceil.

  (* [comment removed for export] *)
  Definition aclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
    SP <= A
    \/ (forall a, A <= a < A + n -> aimg_client a)
    \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b)
    \/ (exists b, In b LB /\ sh (blk_addr b) <= A /\ A + n <= sh (blk_addr b) + nsh (blk_size b))
    \/ (FSB <= A /\ A + n <= FSB + AFS_SIZE) \/ (sh FSB <= A /\ A + n <= sh (FSB + AFS_SIZE))
    \/ (sh aceil <= A /\ A + n <= AHI_LO).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition SR_laws : Prop :=
       (forall (Q : config -> Prop) c, Q c -> SR Q c)
    /\ (forall (Q Q' : config -> Prop) c, SR Q c -> (forall c', Q c' -> Q' c') -> SR Q' c)
    /\ (forall (Q1 Q2 : config -> Prop) c, SR Q1 c -> (forall c', Q1 c' -> SR Q2 c') -> SR Q2 c)
    /\ (forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
          AKREL s (mkCfg msF mo) -> VIS s msF = ms -> evt asegs P ms ->
          (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') -> SR Q (mkCfg msF' mo')) ->
          SR Q (mkCfg msF mo)).

  Definition AKREL_laws : Prop :=
       (forall s c, AKREL s c -> m_halted (cfg_model c) = None)
    (* [comment removed for export] *)
    /\ (forall s R F pc fc rv m ro, exists m', VIS s (MS R F pc fc rv m ro) = MS R F pc fc rv m' ro).

  Definition MPRES_laws : Prop :=
       (forall mo, MPRES mo mo)
    /\ (forall mo1 mo2 mo3, MPRES mo1 mo2 -> MPRES mo2 mo3 -> MPRES mo1 mo3).

  (* [comment removed for export] *)
  Definition alloc_ok_of_live : Prop :=
    forall s LB m n, RHEAP s LB m -> 0 <= n -> lb_bytes LB + n <= as_LIVE_MAX H ->
      Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H -> alloc_ok s LB n.
  (* [comment removed for export] *)
  Definition cost_laws : Prop :=
       (forall n, 0 <= n -> 0 <= Cm n) /\ (forall n n', 0 <= n <= n' -> Cm n <= Cm n')
    /\ (forall n, 0 <= n -> 0 <= Cf n) /\ (forall n n', 0 <= n <= n' -> Cf n <= Cf n')
    (* [comment removed for export] *)
    /\ (forall a b, 0 <= a -> 0 <= b -> Cm a + Cm b <= Cm (a + b))
    /\ (forall a b, 0 <= a -> 0 <= b -> Cf a + Cf b <= Cf (a + b)).

  (* [comment removed for export] *)
  Definition RHEAP_frame : Prop := forall s LB m m' W,
    RHEAP s LB m -> munch W m m' -> wmono asegs m m' -> Forall (aclient_write_ok LB) W -> RHEAP s LB m'.
  Definition RHEAP_block_range : Prop := forall s LB m b, RHEAP s LB m -> In b LB -> ablock_range (blk_addr b) (blk_size b).
  Definition RHEAP_blocks_disjoint : Prop := forall s LB m b1 b2,
    RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
    blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1.   (* [comment removed for export] *)
  Definition RHEAP_blocks_nodup : Prop := forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
  (* [comment removed for export] *)
  Definition RHEAP_shvis : Prop := forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB -> shvis m A (A + n).
  (* [comment removed for export] *)
  Definition RHEAP_fsb : Prop := forall s LB m, RHEAP s LB m -> afsb_ok.
  Definition RHEAP_thr : Prop := forall s LB m, RHEAP s LB m -> athr_cells m.        (* [comment removed for export] *)
  Definition rauxv_frame : Prop := forall LB m m' B W,
    rauxv_ok m B -> munch W m m' -> wmono asegs m m' -> Forall (aclient_write_ok LB) W -> rauxv_ok m' B.
  Definition lb_remove_laws : Prop :=
       (forall p A n LB, ~ In p (map blk_id LB) -> lb_remove p ((p, A, n) :: LB) = LB)
    /\ (forall p b LB, blk_id b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB)
    /\ (forall p LB b, In b (lb_remove p LB) -> In b LB).

  (* [comment removed for export] *)
  Definition RFS_frame : Prop := forall LF m m' W,
    RFS LF m -> munch W m m' -> wmono asegs m m' -> Forall (afs_write_ok LF) W -> RFS LF m'.
  (* [comment removed for export] *)
  Definition RFS_ext : Prop := forall LF m m',
    RFS LF m ->
    (forall a, 0 <= a < 2^64 -> (FSB <= a < FSB + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI \/ sh FSB <= a < sh (FSB + AFS_SIZE)) ->
       m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
    RFS LF m'.
  Definition RFS_range : Prop := forall LF m, RFS LF m -> afsb_ok /\ forall f, In f LF -> aframe_range (ff_class f) (ff_addr f) (ff_flag f).
  Definition RFS_disjoint : Prop := forall LF m f1 f2, RFS LF m -> In f1 LF -> In f2 LF -> ff_addr f1 <> ff_addr f2 ->
    (ff_addr f1 + fsz (ff_class f1) <= ff_addr f2 \/ ff_addr f2 + fsz (ff_class f2) <= ff_addr f1) /\ ff_flag f1 <> ff_flag f2.
  Definition RFS_nodup : Prop := forall LF m, RFS LF m -> List.NoDup (map ff_addr LF).
  Definition RFS_shvis : Prop := forall LF m f, RFS LF m -> In f LF -> shvis m (ff_addr f) (ff_addr f + fsz (ff_class f)).
  (* [comment removed for export] *)
  Definition frame_release_law : Prop := forall LF m m' W k ff fp,
    RFS LF m -> In (k, ff, fp) LF -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => afs_write_ok LF iv \/ (fst iv = fp /\ snd iv = fp + 1)) W ->
    mrd asegs m' (wa fp) = Some (b8 0) ->
    RFS (lf_remove ff LF) m'.

  (* [comment removed for export] *)
  Definition chain_laws : Prop :=
       (* [comment removed for export] *)
       (forall m cur, (cur <= aceil \/ cur mod 8 <> 0) -> CHAIN m cur [])
       (* [comment removed for export] *)
    /\ (forall m cur CH fp ra, CHAIN m cur CH -> 0 <= cur < 2^64 -> 0 <= ra < 2^64 ->
          fp mod 16 = 0 -> aceil + 16 <= fp -> fp < 2^64 ->
          rw_cells asegs m (fp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra)] -> CHAIN m fp ((fp, ra) :: CH))
       (* [comment removed for export] *)
       (* [comment removed for export] *)
    /\ (forall m m' cur CH, CHAIN m cur CH ->
          (forall fp ra a, In (fp, ra) CH -> fp - 16 <= a < fp -> m' (wa a) = m (wa a)) -> CHAIN m' cur CH)
       (* [comment removed for export] *)
    /\ (forall m cur CH fp ra, CHAIN m cur CH -> In (fp, ra) CH -> aceil + 16 <= fp < 2^64 /\ fp mod 8 = 0 /\ 0 <= ra < 2^64).

  (* [comment removed for export] *)
  Definition trace_ok (TRS : list (list Z)) (pc0 : Z) (t : list Z) : Prop :=
    ~ In pc0 t /\ forall j, (1 <= j)%nat -> In (firstn j (pc0 :: t)) TRS.

  (* [comment removed for export] *)
  Definition pf_ok (TRS : list (list Z)) (PF : list (Z * list Z)) (ra : Z) (CH : list (Z * Z)) : Prop :=
    Forall (fun pp : Z * list Z => trace_ok TRS (fst pp) (snd pp ++ ra :: map snd CH)) PF.
  Definition pf_shift (site : Z) (PF : list (Z * list Z)) : list (Z * list Z) :=
    map (fun pp : Z * list Z => (fst pp, snd pp ++ [site])) PF.

  Lemma pf_ok_call : forall TRS PFf PFg raf fpf CHf site,
    pf_ok TRS PFf raf CHf -> incl (pf_shift site PFg) PFf -> pf_ok TRS PFg site ((fpf, raf) :: CHf).
  Proof.
    intros TRS PFf PFg raf fpf CHf site OK INC. unfold pf_ok in *. apply Forall_forall. intros [pc0 p] IN. cbn.
    assert (IN' : In (pc0, p ++ [site]) PFf). { apply INC. unfold pf_shift. apply in_map_iff. exists (pc0, p). split; [reflexivity| exact IN]. }
    pose proof (proj1 (Forall_forall _ _) OK _ IN') as T. cbn in T. rewrite <- app_assoc in T. exact T.
  Qed.
  Lemma pf_ok_site : forall TRS PF ra CH pc0 p,
    pf_ok TRS PF ra CH -> In (pc0, p) PF -> trace_ok TRS pc0 (p ++ ra :: map snd CH).
  Proof. intros TRS PF ra CH pc0 p OK IN. exact (proj1 (Forall_forall _ _) OK _ IN). Qed.
  Lemma pf_ok_incl : forall TRS PF PF' ra CH, pf_ok TRS PF ra CH -> incl PF' PF -> pf_ok TRS PF' ra CH.
  Proof. intros TRS PF PF' ra CH OK INC. apply Forall_forall. intros pp IN. exact (proj1 (Forall_forall _ _) OK _ (INC _ IN)). Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition malloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) junk (p : bptr) (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
      /\ apres LB (bv_unsigned sp) m m'
      /\ ablock_range A n /\ RHEAP s' ((p, A, n) :: LB) m'
      /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
      /\ addressable m' A n
      /\ ACONST m'
      /\ AL s' >= AL s - Cm n.

  (* [comment removed for export] *)
  Definition malloc_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (n lo B : Z) (errv : word) (mo : Model)
           (CH : list (Z * Z)),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> alloc_ok s LB n -> Cm n <= AL s ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->                 (* [comment removed for export] *)
      ACONST m ->
      CHAIN m (bv_unsigned s0) CH -> trace_ok TR APC0_MALLOC (bv_unsigned ra :: map snd CH) ->
      a0 = Z_to_bv 64 n -> 1 <= n <= 2^28 ->             (* [comment removed for export] *)
      SR (malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo) (mkCfg msF mo).

  Definition malloc_stmt : Prop := malloc_stmt_at AMALLOC_STUB AMALLOC_STACK.

  (* [comment removed for export] *)
  Definition free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (n lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv]
      /\ rauxv_ok m' B
      /\ apres (lb_remove p LB) (bv_unsigned sp) m m'
      /\ RHEAP s' (lb_remove p LB) m'
      /\ ACONST m'
      /\ AL s' >= AL s - Cf n.

  (* [comment removed for export] *)
  Definition free_stmt_at (entry pc0 : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (mo : Model)
           (CH : list (Z * Z)) (bs sbs : list byte),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> In (p, A, n) LB -> Cf n <= AL s ->
      rw_cells asegs m A [CB (Z.to_nat n) bs] -> SHAD m A sbs -> Z.of_nat (length sbs) = nsh n ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->                 (* [comment removed for export] *)
      ACONST m ->
      CHAIN m (bv_unsigned s0) CH -> trace_ok TR pc0 (bv_unsigned ra :: map snd CH) ->
      a0 = Z_to_bv 64 A ->
      SR (free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n lo B errv m mo) (mkCfg msF mo).

  Definition free_stmt   : Prop := free_stmt_at AFREE_STUB APC0_FREE.

  (* [comment removed for export] *)
  Definition free_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ rauxv_ok m' B
      /\ apres LB (bv_unsigned sp) m m'
      /\ RHEAP s' LB m'
      /\ ACONST m'
      /\ AL s' >= AL s - Cf 0.
  Definition free_null_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (lo B : Z) (errv : word) (mo : Model)
           (CH : list (Z * Z)),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> Cf 0 <= AL s ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->                 (* [comment removed for export] *)
      ACONST m ->
      CHAIN m (bv_unsigned s0) CH ->      (* [comment removed for export] *)
      SR (free_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition stack_malloc_post (k : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z) junk1 junk2,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AFS_STACK, bv_unsigned sp); (FSB, FSB + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz k); (sh ff, sh ff + fshn k)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ RFS ((k, ff, fp) :: LF) m'
      /\ rw_cells asegs m' ff [CB 24 junk1; C8 sp; CB (Z.to_nat (fsz k - 40)) junk2; C8 (Z_to_bv 64 fp)]
      /\ SHAD m' ff (poison_bytes (Z.to_nat (fshn k)) 0)
      /\ rw_cells asegs m' fp [C1 (b8 1)]
      /\ ACONST m'.

  Definition stack_malloc_stmt (k entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (lo : Z),
      RFS LF m -> (length LF < AFS_MAXLIVE)%nat ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
      evt asegs (stack_malloc_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

  Definition stack_malloc_1_stmt : Prop := stack_malloc_stmt 1 AFS_MALLOC_1.
  Definition stack_malloc_4_stmt : Prop := stack_malloc_stmt 4 AFS_MALLOC_4.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition set_shadow_post (v : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sa n : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(sa, sa + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' sa [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) v)].
  Definition set_shadow_stmt (v entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa n : Z) junk,
      a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      rw_cells asegs m sa [CB (Z.to_nat n) junk] -> mem_inv asegs m -> ACONST m ->
      evt asegs (set_shadow_post v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sa n m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition set_shadow_f5_stmt : Prop := set_shadow_stmt 0xf5 ASET_SHADOW_F5.

  (* [comment removed for export] *)
  Definition amemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 a1 a2 : word) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
      /\ bytes_at asegs m' (bv_unsigned a1) src
      /\ ACONST m'.
  Definition amemcpy_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (src junk : list byte) (lo : Z),
      bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
      rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
      (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
      accessible m (bv_unsigned a1) (bv_unsigned a2) -> accessible m (bv_unsigned a0) (bv_unsigned a2) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      (* [comment removed for export] *)
      bv_unsigned a2 <= 2^40 ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt asegs (amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition asan_memcpy_stmt : Prop := amemcpy_stmt_at AASAN_MEMCPY.
  Definition memcpy_icpt_stmt : Prop := amemcpy_stmt_at AMEMCPY_STUB.

  (* [comment removed for export] *)
  Definition amemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 a2 : word) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
      /\ ACONST m'.
  Definition amemmove_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (src junk : list byte) (lo : Z),
      bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
      rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
      (* [comment removed for export] *)
      (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
      accessible m (bv_unsigned a1) (bv_unsigned a2) -> accessible m (bv_unsigned a0) (bv_unsigned a2) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      bv_unsigned a2 <= 2^40 ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt asegs (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 src lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition asan_memmove_stmt : Prop := amemmove_stmt_at AASAN_MEMMOVE.

  (* [comment removed for export] *)
  Definition amemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 a2 : word) (c : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) (poison_bytes (Z.to_nat (bv_unsigned a2)) c)]
      /\ ACONST m'.
  Definition asan_memset_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (c : Z) (junk : list byte) (lo : Z),
      a1 = Z_to_bv 64 c -> 0 <= c < 256 ->
      rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
      accessible m (bv_unsigned a0) (bv_unsigned a2) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      bv_unsigned a2 <= 2^40 -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      evt asegs (amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 c lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition astrlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 : word) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack)
      /\ ACONST m'.
  Definition strlen_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (str slack : list byte) (lo : Z),
      bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
      ~ In (Z_to_bv 8 0) str ->
      ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)) ->
      accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      Z.of_nat (length str) + 1 <= 2^40 -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
      (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      evt asegs (astrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRLEN_STUB) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition zstrncmp (e t : list Z) (n : nat) : Z :=
    (fix go (e t : list Z) (n : nat) {struct n} : Z :=
       match n with O => 0 | S n' =>
         match e, t with
         | [], [] => 0 | [], c2 :: _ => 0 - c2 | c1 :: _, [] => c1
         | c1 :: e', c2 :: t' => if Z.eqb c1 c2 then (if Z.eqb c1 0 then 0 else go e' t' n') else c1 - c2
         end end) e t n.
  Definition astrncmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ sx32 a0 = a0 /\ (r = 0 <-> bv_signed (sx32 a0) = 0) /\ (r < 0 <-> bv_signed (sx32 a0) < 0)
      /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ ACONST m'.
  Definition strncmp_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e t rest1 rest2 : list Z) (n : Z) (lo : Z),
      a2 = Z_to_bv 64 n -> 0 <= n -> Z.of_nat (length e) <= n ->
      bytes_at asegs m (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)) -> Forall (fun c => 0 < c < 256) e ->
      bytes_at asegs m (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)) -> Forall (fun c => 0 < c < 256) t ->
      accessible m (bv_unsigned a0) (Z.min n (Z.of_nat (length e) + 1)) ->
      accessible m (bv_unsigned a1) (Z.min n (Z.of_nat (length t) + 1)) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      n <= 2^40 ->
      in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.min n (Z.of_nat (length e) + 1)) ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)) ->
      (bv_unsigned a0 + Z.of_nat (length (e ++ 0 :: rest1)) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + Z.of_nat (length (t ++ 0 :: rest2)) <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt asegs (astrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (zstrncmp e t (Z.to_nat n)) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRNCMP_STUB) fc None m (seg_rom asegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition asan_rt_hyps : Prop :=
    SR_laws /\ AKREL_laws /\ MPRES_laws /\ alloc_ok_of_live /\ cost_laws
    /\ RHEAP_frame /\ RHEAP_block_range /\ RHEAP_blocks_disjoint /\ RHEAP_blocks_nodup /\ RHEAP_shvis /\ RHEAP_fsb /\ RHEAP_thr
    /\ rauxv_frame /\ lb_remove_laws
    /\ RFS_frame /\ RFS_ext /\ RFS_range /\ RFS_disjoint /\ RFS_nodup /\ RFS_shvis /\ frame_release_law
    /\ chain_laws
    /\ malloc_stmt /\ free_stmt
    /\ free_null_stmt_at AFREE_STUB
    /\ stack_malloc_1_stmt /\ stack_malloc_4_stmt /\ set_shadow_f5_stmt
    /\ asan_memcpy_stmt /\ asan_memset_stmt /\ asan_memmove_stmt /\ memcpy_icpt_stmt
    /\ strlen_icpt_stmt /\ strncmp_icpt_stmt.   (* [comment removed for export] *)
End Iface.

(* [comment removed for export] *)
