(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap ECH_Xpres AsStack0 AsAuxv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition P_FUZZ_ENTRY : Z := 0x1ef1d0.      (* [comment removed for export] *)
Definition P_FUZZ_RA : Z := 0x1ef0c8.         (* [comment removed for export] *)
Definition AFUZZ_EMPTY : Z := 0xbdcf60.

(* [comment removed for export] *)
Definition AFUZZ_STACK : Z := 16384.

(* [comment removed for export] *)
Definition AFUZZ_LIVE : Z := 2^24.
Definition ATRANS_CNT : Z := 1024.
Definition ALIB_CNT_MAX : Z := 1800.
Definition ALIB_BYTES_MAX : Z := 2^17.

(* [comment removed for export] *)
Definition ACLEANUP : Z := 0xbdd440.

(* [comment removed for export] *)
Definition arelro_lib (m : mem) : Prop := forall i, 0x571000 <= i < 0x5ea000 -> m (wa i) = None.

(* [comment removed for export] *)
Definition alibx_ok (a : Z) : Prop :=
  (0x5ed1a0 <= a < 0x5edca8) \/ (0xbdcf70 <= a < 0xbe1be8) \/ (0xbe1bf0 <= a < 0xbe1c38) \/ (0xc03040 <= a < 0xc03570)
  \/ (0xc02bf8 <= a < 0xc03010) \/ (0x5edf88 <= a < 0x5edf90).
  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition alibw_ok (a : Z) : Prop := alibx_ok a \/ (0xbe1bec <= a < 0xbe1bf0).

(* [comment removed for export] *)
Definition in_lblock (LIB : list block) (a : Z) : Prop := exists b, In b LIB /\ blk_addr b <= a < blk_addr b + blk_size b.
(* [comment removed for export] *)
Definition in_lblock_sh (LIB : list block) (a : Z) : Prop := exists b, In b LIB /\ sh (blk_addr b) <= a < sh (blk_addr b) + nsh (blk_size b).

(* [comment removed for export] *)
Definition amagree (R : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> R a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

(* [comment removed for export] *)
Definition AMUSL0_CELLS : list (Z * list cell) :=
  [(0xc02bf8, [C8 (wz 0x1c18d4)]); (0xc02ff8, [C4 (wz 0)]); (0xc03000, [C8 (wz 0); C8 (wz 0)]); (0xbe1bfa, [C1 (b8 1)])].
Definition amusl0 (m : mem) : Prop := Forall (fun ac => rw_cells asegs m (fst ac) (snd ac)) AMUSL0_CELLS.

Lemma bytes_at_agree_eq : forall m m' A bs,
  bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a)) -> bytes_at asegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & HB) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd. rewrite (HE (A + Z.of_nat i) ltac:(lia)). reflexivity.
Qed.
Lemma rw_cells_agree_eq : forall m m' A cs,
  rw_cells asegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
  rw_cells asegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] (W0 & W1 & HW)] HE. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree_eq; [exact HB|]. rewrite cells_bytes_length by assumption. intros a Ha. exact (proj1 (HE a Ha)).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (HE (A + i) ltac:(lia))). apply HW. exact Hi.
Qed.
Lemma amusl0_cells_libx : Forall (fun ac : Z * list cell => forall a, fst ac <= a < fst ac + Z.of_nat (cells_size (snd ac)) -> alibx_ok a) AMUSL0_CELLS.
Proof. unfold AMUSL0_CELLS, alibx_ok. repeat (constructor; [cbn; intros; lia|]). constructor. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amusl0_agree : forall m m', amusl0 m ->
  (forall a, 0 <= a < 2^64 -> alibx_ok a -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
  amusl0 m'.
Proof.
  intros m m' HM HE. unfold amusl0 in *. apply Forall_forall. intros ac Hin.
  pose proof (proj1 (Forall_forall _ _) HM ac Hin) as HC. pose proof (proj1 (Forall_forall _ _) amusl0_cells_libx ac Hin) as HX.
  eapply rw_cells_agree_eq; [exact HC |].
  intros a Ha. pose proof (HX a Ha) as Hx. apply HE; [unfold alibx_ok in Hx; lia | exact Hx].
Qed.
(* [comment removed for export] *)
Lemma amusl0_frame : forall W m m', amusl0 m -> munch W m m' -> wmono asegs m m' ->
  (forall x, alibx_ok x -> outside W x) -> amusl0 m'.
Proof.
  intros W m m' HM MU WM HO. eapply amusl0_agree; [exact HM|]. intros a Ha64 Hx. split.
  - unfold wa. apply MU. rewrite unsigned_lit; [apply HO; exact Hx | exact Ha64].
  - intros Wv. apply WM. exact Wv.
Qed.

(* [comment removed for export] *)
Record alib : Type := ALIB {
  al_st       : Type;                               (* [comment removed for export] *)
  al_fresh    : al_st;                              (* [comment removed for export] *)
  al_is_fresh : al_st -> bool;
  al_LIBST    : al_st -> list block -> mem -> Prop; (* [comment removed for export] *)
  al_LIBX0    : list (Z * Z);                       (* [comment removed for export] *)
  al_LIBX     : list (Z * Z);                       (* [comment removed for export] *)
  al_frames   : nat;                                (* [comment removed for export] *)
  al_cost     : asr -> Z -> Z;                      (* [comment removed for export] *)
  al_PF       : list (Z * list Z);                  (* [comment removed for export] *)
  al_tr_ok    : asr -> Prop                         (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition afuzz_cnt (L : alib) (st : al_st L) : Z := (if al_is_fresh L st then ALIB_CNT_MAX else 0) + ATRANS_CNT.
Definition afuzz_live (L : alib) (st : al_st L) : Z := (if al_is_fresh L st then ALIB_BYTES_MAX else 0) + AFUZZ_LIVE.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Record alib_ok (L : alib) : Prop := ALIBOK {
  alo_fresh : forall m, (forall a, rin_ivs (al_LIBX0 L) a -> m (wa a) = None) -> amusl0 m -> al_LIBST L (al_fresh L) [] m;   (* [comment removed for export] *)
  alo_fresh_b : al_is_fresh L (al_fresh L) = true;
  alo_nil   : forall st LIB m, al_LIBST L st LIB m -> al_is_fresh L st = true -> LIB = [];
  alo_frame : forall st LIB m m', al_LIBST L st LIB m ->
                amagree (fun a => rin_ivs (al_LIBX L) a \/ in_lblock LIB a \/ in_lblock_sh LIB a) m m' -> al_LIBST L st LIB m';   (* [comment removed for export] *)
  alo_sub   : forall a, rin_ivs (al_LIBX0 L) a -> rin_ivs (al_LIBX L) a;
  alo_libx  : forall a, rin_ivs (al_LIBX L) a -> alibx_ok a;                      (* [comment removed for export] *)
  alo_libx_wf : Forall (fun iv : Z * Z => fst iv < snd iv) (al_LIBX L);            (* [comment removed for export] *)
  alo_clean : forall st LIB m, al_LIBST L st LIB m -> m (wa ACLEANUP) = None;
  alo_cost0 : forall H n, asan_rt_hyps H -> 0 <= n -> 0 <= al_cost L H n;
  alo_costm : forall H n n', asan_rt_hyps H -> 0 <= n <= n' -> al_cost L H n <= al_cost L H n';
  alo_frames : (al_frames L <= AFS_MAXLIVE)%nat
}.

Section W.
  Variable H : asr.
  Variable L : alib.

  Definition fuzz_cost (N : Z) : Z := al_cost L H N.
  (* [comment removed for export] *)
  Definition AERRNO_X : list (Z * Z) := [(ATP - 164, ATP - 164 + 4)].

  Definition fuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LIB LBc : list block) (st : al_st L) (LF : list fframe) (N lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LIB' LBc' : list block) (st' : al_st L)
                    (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ arelro_lib m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' (LIB' ++ LBc') m' /\ Permutation LBc' LBc
      /\ al_LIBST L st' LIB' m' /\ al_is_fresh L st' = false
      /\ Z.of_nat (length LIB') <= ALIB_CNT_MAX /\ lb_bytes LIB' <= ALIB_BYTES_MAX
      /\ (al_is_fresh L st = false -> LIB' = LIB)
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LBc (bv_unsigned sp) (AERRNO_X ++ al_LIBX L ++ XS) m m'
      (* [comment removed for export] *)
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - fuzz_cost N.

  Definition fuzz_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LIB LBc : list block) (st : al_st L) (LF : list fframe) (CH : list (Z * Z))
           (D N lo B shi : Z) (ds : list byte) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 P_FUZZ_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N ->
      (* [comment removed for export] *)
      bytes_at asegs m D ds -> Z.of_nat (length ds) = N -> N < 2^26 -> D mod 16 = 0 ->
      (1 <= N -> exists pD, In (pD, D, N) LBc) -> (N = 0 -> D = AFUZZ_EMPTY) ->
      (* [comment removed for export] *)
      as_RHEAP H s (LIB ++ LBc) m -> as_AKREL H s (mkCfg msF mo) -> al_LIBST L st LIB m ->
      lb_bytes (LIB ++ LBc) + afuzz_live L st <= as_LIVE_MAX H ->
      Z.of_nat (length (LIB ++ LBc)) + afuzz_cnt L st <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> aauxv_ok m B -> bv_unsigned sp <= B -> B < 2^64 ->     (* [comment removed for export] *)
      (* [comment removed for export] *)
      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFUZZ_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> arelro_lib m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      (* [comment removed for export] *)
      ACONST m ->
      (1 <= N -> addressable m D N) ->
      as_RFS H LF m -> (length LF + al_frames L <= AFS_MAXLIVE)%nat ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) (al_PF L) (bv_unsigned ra) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      al_tr_ok L H ->
      fuzz_cost N <= as_AL H s ->
      as_SR H (fuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LBc st LF N lo B shi m mo)
        (mkCfg msF mo).
End W.

End HCW.
