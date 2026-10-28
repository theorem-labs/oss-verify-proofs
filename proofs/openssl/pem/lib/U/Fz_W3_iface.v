(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_FUZZ_ONE : Z := 0xe1aec.          (* [comment removed for export] *)
Definition FZ_PEM_READ_BIO : Z := 0x187f60.      (* [comment removed for export] *)
Definition FZ_SANITIZE : Z := 0x1888c0.          (* [comment removed for export] *)
Definition FZ_PEM_MALLOC : Z := 0x188824.
Definition FZ_PEM_FREE : Z := 0x18886c.
Definition FZ_BIO_NEW : Z := 0x10b8c8.           (* [comment removed for export] *)
Definition FZ_BIO_FREE : Z := 0x10b8f0.
Definition FZ_BIO_READ : Z := 0x10bd14.
Definition FZ_BIO_WRITE : Z := 0x10bf9c.
Definition FZ_BIO_PUTS : Z := 0x10c30c.
Definition FZ_BIO_GETS : Z := 0x10c4f4.
Definition FZ_BIO_CTRL : Z := 0x10bba8.
Definition FZ_EVP_CTX_NEW : Z := 0x191924.
Definition FZ_EVP_CTX_FREE : Z := 0x191954.
Definition FZ_ERR_NEW : Z := 0xe747c.
Definition FZ_ERR_SET_DEBUG : Z := 0xe7638.
Definition FZ_ERR_SET_ERROR : Z := 0xe77dc.
Definition FZ_ERR_CLEAR : Z := 0xe80c8.
Definition M_MEM : Z := 0x2d3fc8.                (* [comment removed for export] *)
Definition M_SECMEM : Z := 0x2d4038.             (* [comment removed for export] *)
Definition PEM_FLAG_SECURE : Z := 1.
Definition PEM_FLAG_EAY_COMPATIBLE : Z := 2.
Definition PEM_FLAG_ONLY_B64 : Z := 4.
Definition LBUF : Z := 256.                      (* [comment removed for export] *)
Definition fsec (flags : Z) : Z := Z.land flags 1.
Definition msec (meth : Z) : Z := if Z.eqb meth M_SECMEM then 1 else 0.

(* [comment removed for export] *)
Definition cpostx (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m : mem) (lo B : Z)
    (T : bptr -> Prop) (W : list (Z * Z)) (FB : Z) (EV : nat) (da db dbig : Z)
    (R : word -> list block -> @clist bptr -> mem -> Prop) : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f' L' s' ms' => exists v m' LBall',
    cret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v m' ms'
    /\ (f - EV <= f')%nat /\ cgrow L L' da db dbig
    /\ cstate s' LBall' LB L' m' sp tp lo B
    /\ cframe T W FB s LBall L m s' LBall' L' m'
    /\ R v LBall' L' m'.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record mbk : Type := MBK { k_bi : bptr; k_bb : bptr; k_bm : bptr; k_rp : bptr; k_d : option bptr }.
Definition mbio_T (K : mbk) : bptr -> Prop := fun q => q = k_bi K \/ q = k_bb K \/ q = k_bm K \/ q = k_rp K \/ k_d K = Some q.
Definition mbk_data (K : mbk) (pd : option bptr) : mbk := MBK (k_bi K) (k_bb K) (k_bm K) (k_rp K) pd.

(* [comment removed for export] *)
Definition bio_head (meth : Z) : list cell := [C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Definition bio_tail (nr nw : word) : list cell := [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)].

Definition mbio_blocks (K : mbk) : list bptr := [k_bi K; k_bb K; k_bm K; k_rp K] ++ match k_d K with Some q => [q] | None => [] end.

(* [comment removed for export] *)
Definition mb_inner (m : mem) (LBall : list block) (L : @clist bptr) (K : mbk) (BB BM RP len max off : Z) (flw blw : word) : Prop :=
  exists rmaxw : word,
     cown LBall L (k_bb K) BB 16 16 /\ rw_cells usegs m BB [C8 (wz BM); C8 (wz RP)] /\ cown LBall L (k_bm K) BM 32 32 /\ cown LBall L (k_rp K) RP 32 32
  /\ 0 <= off <= len /\ len <= max /\ max < 2^31 - 1
  /\ match k_d K with
     | None => max = 0 /\ rw_cells usegs m BM [C8 blw; C8 (wz 0); C8 (wz 0); C8 flw] /\ rw_cells usegs m RP (readp_cells 0 0 0 rmaxw flw)
     | Some pd => exists (D nm : Z) (junk : list byte), cown LBall L pd D max nm /\ 0 < max /\ rw_cells usegs m BM [C8 blw; C8 (wz D); C8 (wz max); C8 flw]
                  /\ rw_cells usegs m RP (readp_cells len D off rmaxw flw) /\ length junk = Z.to_nat max /\ rw_cells usegs m D [CB (Z.to_nat max) junk]
     end.

(* [comment removed for export] *)
Definition mbio_repx (m : mem) (LBall : list block) (L : @clist bptr) (K : mbk) (BI BM : Z) (blw : word) (meth len max off : Z) : Prop :=
  exists (BB RP fl : Z) (rrw padw nr nw : word),
     cown LBall L (k_bi K) BI 128 128 /\ List.NoDup (mbio_blocks K) /\ (meth = M_MEM \/ meth = M_SECMEM)
  /\ rw_cells usegs m BI (bio_head meth)
  /\ rw_cells usegs m (BI + 40) (bio_w1_cells (wz 4294967297) fl rrw (wz 4294967295) padw (wz BB)) /\ fl_ok fl
  /\ rw_cells usegs m (BI + 72) (bio_tail nr nw)
  /\ mb_inner m LBall L K BB BM RP len max off (wz (msec meth)) blw.
Definition mbio_rep (m : mem) (LBall : list block) (L : @clist bptr) (K : mbk) (BI meth len max off : Z) : Prop :=
  exists BM, mbio_repx m LBall L K BI BM (wz len) meth len max off.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PMAL_STACK : Z := 16 + CSM_STACK.
Definition PFREE_STACK : Z := 16 + CSF_STACK.

Definition pem_malloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (n flags lo B : Z),
  (1 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 < n < 2^31 -> 0 <= flags < 2^32 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PMAL_STACK -> a0 = wz n -> a1 = wz flags ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz FZ_PEM_MALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
                (cs_malloc_res n LBall L)).

Definition pem_malloc0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (flags lo B : Z),
  0 <= flags < 2^32 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PMAL_STACK -> a0 = wz 0 -> a1 = wz flags ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz FZ_PEM_MALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 0 0 0 0
                (fun v LBall' L' _ => v = wz 0 /\ LBall' = LBall /\ L' = L)).

Definition pem_free_res (p : bptr) (nm : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L.

Definition pem_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat)
         (p : bptr) (A n nm num flags lo B : Z) (junk : list byte),
  (1 <= f)%nat -> cown LBall L p A n nm -> 0 <= num <= n -> rw_cells usegs m A [CB (Z.to_nat num) junk] -> 0 <= flags < 2^32 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PFREE_STACK -> a0 = wz A -> a1 = wz flags -> a2 = wz num ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz FZ_PEM_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
                (pem_free_res p nm LBall L)).

Definition pem_free_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (flags lo B : Z),
  0 <= flags < 2^32 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PFREE_STACK -> a0 = wz 0 -> a1 = wz flags ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz FZ_PEM_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 0 0 0 0
                (fun _ LBall' L' _ => LBall' = LBall /\ L' = L)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SAN_STACK : Z := 112.

Definition sanitize_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (LB len lo : Z) (bs : list byte) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (len' : Z) (bs' : list byte) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz len') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ 1 <= len' <= len + 1
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (LB, LB + 256)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ length bs' = 256%nat /\ rw_cells usegs m' LB [CB 256 bs']
    /\ nth_error bs' (Z.to_nat (len' - 1)) = Some (Z_to_bv 8 10) /\ nth_error bs' (Z.to_nat len') = Some (Z_to_bv 8 0).

Definition sanitize_line_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB len flags fcall lo : Z) (bs : list byte),
  a0 = wz LB -> a1 = wz len -> a2 = wz flags -> a3 = wz fcall -> 0 < LB -> LB + 256 <= alloc_ceiling ->
  1 <= len <= 254 -> 0 <= flags < 2^32 -> 0 <= fcall < 2^32 ->
  length bs = 256%nat -> rw_cells usegs m LB [CB 256 bs] -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SAN_STACK -> mem_inv usegs m ->
  evt usegs (sanitize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB len lo bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_SANITIZE) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CallIface.
  (* [comment removed for export] *)
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.           (* [comment removed for export] *)
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Definition incl_blocks (LBL LBall : list block) : Prop := forall b, In b LBL -> In b LBall.
  (* [comment removed for export] *)
  Variable errst_at_rest : Z -> list block -> mem -> Prop.                  (* [comment removed for export] *)
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.           (* [comment removed for export] *)
  Variable errst_fp : Z -> list block -> Z -> Prop.                         (* [comment removed for export] *)
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ERRN_STACK : Z := 48 + 64 + 8192.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition err_new_rest_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (pe : bptr) (E enm lo B : Z),
    cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - ERRN_STACK -> libenv m LBL E -> incl_blocks LBL LBall -> cown LBall L pe E 904 enm -> errst_at_rest E [] m ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_ERR_NEW) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq pe) [] 0 0 0 0
         (fun _ LBall' L' m' => LBall' = LBall /\ L' = L /\ libenv m' LBL E /\ errst_live E 1 0 [] m')).

  (* [comment removed for export] *)
  Definition err_set_debug_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (pe : bptr) (E enm SF nf SN nn line lo B : Z)
           (fstr nstr fslack nslack : list byte),
    (2 <= f)%nat -> croom L 2 0 0 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - (96 + ERRN_STACK) -> libenv m LBL E -> incl_blocks LBL LBall -> cown LBall L pe E 904 enm ->
    errst_live E 1 0 [] m ->
    a0 = wz SF -> a1 = wz line -> a2 = wz SN ->
    (* [comment removed for export] *)
    ro_bytes usegs SF (fstr ++ Z_to_bv 8 0 :: fslack) -> ro_bytes usegs SN (nstr ++ Z_to_bv 8 0 :: nslack) -> ~ In (Z_to_bv 8 0) fstr -> ~ In (Z_to_bv 8 0) nstr ->
    (- (SF + nf)) mod 8 <= Z.of_nat (length fslack) -> (- (SN + nn)) mod 8 <= Z.of_nat (length nslack) ->
    0x10000 <= SF -> SF + nf + Z.of_nat (length fslack) <= 0x2c0000 -> 0x10000 <= SN -> SN + nn + Z.of_nat (length nslack) <= 0x2c0000 ->
    nf = Z.of_nat (length fstr) + 1 -> nn = Z.of_nat (length nstr) + 1 -> 1 < nf <= 64 -> 1 < nn <= 64 ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_ERR_SET_DEBUG) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq pe) [] 2 2 0 0
         (fun _ LBall' L' m' => exists (qf qn : bptr) (QF QN : Z), LBall' = (qn, QN, nn) :: (qf, QF, nf) :: LBall /\ L' = (qn, nn) :: (qf, nf) :: L
              /\ libenv m' LBL E /\ errst_live E 1 0 [(qn, QN, nn); (qf, QF, nf)] m')).

  (* [comment removed for export] *)
  Definition err_set_error_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (pe : bptr) (E enm lib reason lo B : Z) (strs : list block),
    cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - (128 + 112 + ERRN_STACK) -> libenv m LBL E -> incl_blocks LBL LBall -> cown LBall L pe E 904 enm -> errst_live E 1 0 strs m ->
    a0 = wz lib -> a1 = wz reason -> a2 = wz 0 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2^31 ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_ERR_SET_ERROR) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq pe) [] 0 0 0 0
         (fun _ LBall' L' m' => LBall' = LBall /\ L' = L /\ libenv m' LBL E /\ errst_live E 1 0 strs m')).

  (* [comment removed for export] *)
  Definition err_clear_steady_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (pe : bptr) (E enm top bot lo B : Z) (strs : list block),
    (length strs <= f)%nat -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - (64 + ERRN_STACK) -> libenv m LBL E -> incl_blocks LBL LBall ->
    (* [comment removed for export] *)
    (forall b, In b LBL -> ~ In (blk_id b) (map blk_id strs)) ->
    cown LBall L pe E 904 enm ->
    errst_live E top bot strs m ->
    (* [comment removed for export] *)
    Forall (fun b => cown LBall L (blk_id b) (blk_addr b) (blk_size b) (blk_size b) /\ blk_id b <> pe) strs ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_ERR_CLEAR) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun q => q = pe \/ In q (map blk_id strs)) [] (length strs) 0 0 0
         (fun _ LBall' L' m' => (forall b, In b LBall' <-> (In b LBall /\ ~ In b strs)) /\ (forall q nm, In (q, nm) L' <-> (In (q, nm) L /\ ~ In q (map blk_id strs)))
              /\ libenv m' LBL E /\ errst_at_rest E [] m')).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BNEW_STACK : Z := 48 + 48 + 32 + 32 + 32 + 48 + 8192.   (* [comment removed for export] *)
  Definition BFREE_STACK : Z := 32 + 32 + 32 + 32 + 32 + 64 + 16 + 8192.   (* [comment removed for export] *)
  Definition BGETS_STACK : Z := 48 + 128.
  Definition BPUTS_STACK : Z := 48 + 32 + WRITE_STACK.     (* [comment removed for export] *)
  Definition BWRITE_STACK : Z := 32 + 64 + 32 + WRITE_STACK. (* [comment removed for export] *)
  Definition BREAD_STACK : Z := 32 + 80 + 32 + 80.     (* [comment removed for export] *)
  Definition BCTRL_STACK : Z := 48 + 96.         (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bio_new_res (meth : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun v LBall' L' m' => exists (K : mbk) (BI BB BM RP : Z),
         v = wz BI /\ k_d K = None
      /\ LBall' = (k_rp K, RP, 32) :: (k_bm K, BM, 32) :: (k_bb K, BB, 16) :: (k_bi K, BI, 128) :: LBall /\ L' = (k_rp K, 32) :: (k_bm K, 32) :: (k_bb K, 16) :: (k_bi K, 128) :: L
      /\ mbio_rep m' LBall' L' K BI meth 0 0 0.
  Definition bio_new_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (meth E lo B : Z),
    (4 <= f)%nat -> croom L 4 0 0 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - BNEW_STACK -> libenv m LBL E -> incl_blocks LBL LBall ->
    a0 = wz meth -> (meth = M_MEM \/ meth = M_SECMEM) ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_NEW) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 4 4 0 0
         (fun v LBall' L' m' => libenv m' LBL E /\ bio_new_res meth LBall L v LBall' L' m')).

  (* [comment removed for export] *)
  Definition bio_free_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (K : mbk) (BI BM meth len max off E lo B : Z) (blw : word),
    (5 <= f)%nat -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - BFREE_STACK -> bv_unsigned sp mod 16 = 0 -> libenv m LBL E -> incl_blocks LBL LBall ->
    (forall b, In b LBL -> ~ mbio_T K (blk_id b)) -> mbio_repx m LBall L K BI BM blw meth len max off ->
    a0 = wz BI ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_FREE) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (mbio_T K) [] (length (mbio_blocks K)) 0 0 0
         (fun v LBall' L' m' => v = wz 1 /\ libenv m' LBL E
              /\ (forall b, In b LBall' <-> (In b LBall /\ ~ In (blk_id b) (mbio_blocks K))) /\ (forall q nm, In (q, nm) L' <-> (In (q, nm) L /\ ~ In q (mbio_blocks K))))).

  (* [comment removed for export] *)
  Definition bio_gets_res (K : mbk) (BI meth len max off LB : Z) (bs : list byte) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun v LBall' L' m' => exists (k : Z) (bs' : list byte), v = wz k /\ LBall' = LBall /\ L' = L /\ length bs' = 256%nat /\ rw_cells usegs m' LB [CB 256 bs']
      /\ ((k = 0 /\ off = len /\ mbio_rep m' LBall L K BI meth len max off)
          \/ (1 <= k <= Z.min (len - off) 254 /\ nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 0) /\ mbio_rep m' LBall L K BI meth len max (off + k))).
  Definition bio_gets_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (pl : bptr) (BI meth len max off LB lo B : Z)
           (bs : list byte),
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - BGETS_STACK -> mbio_rep m LBall L K BI meth len max off ->
    cown LBall L pl LB 256 256 -> ~ mbio_T K pl -> length bs = 256%nat -> rw_cells usegs m LB [CB 256 bs] ->
    a0 = wz BI -> a1 = wz LB -> a2 = wz 255 ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_GETS) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun q => mbio_T K q \/ q = pl) [] 0 0 0 0
         (bio_gets_res K BI meth len max off LB bs LBall L)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition puts_lists (K : mbk) (pd' : option bptr) (max max' : Z) (LBall : list block) (L : @clist bptr) (LBall' : list block) (L' : @clist bptr) : Prop :=
       (pd' = k_d K /\ max' = max /\ LBall' = LBall /\ L' = L)
    \/ (exists (q : bptr) (D : Z), pd' = Some q /\ k_d K = None /\ LBall' = (q, D, max') :: LBall /\ L' = (q, max') :: L)
    \/ (exists (q : bptr) (D : Z) (d : bptr) (i : nat) (nm : Z), pd' = Some q /\ k_d K = Some d /\ LBall' = (q, D, max') :: lb_remove d LBall
                                                      /\ nth_error L i = Some (d, nm) /\ L' = (q, max') :: cremove i L).
  Definition bio_puts_res (K : mbk) (BI meth len max n : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun v LBall' L' m' => exists (pd' : option bptr) (max' : Z), v = wz n /\ (max' = max \/ max' = grow_n (len + n)) /\ len + n <= max'
      /\ mbio_rep m' LBall' L' (mbk_data K pd') BI meth (len + n) max' 0
      /\ (forall b, In b LBall -> ~ (k_d K = Some (blk_id b)) -> In b LBall') /\ (forall q nm, In (q, nm) L -> ~ (k_d K = Some q) -> In (q, nm) L')
      /\ (forall b, In b LBall' -> In b LBall \/ pd' = Some (blk_id b)) /\ (forall q nm, In (q, nm) L' -> In (q, nm) L \/ pd' = Some q)
      /\ puts_lists K pd' max max' LBall L LBall' L'.
  Definition bio_puts_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (pl : bptr) (BI meth len max LB n lo B : Z)
           (bs : list byte),
    (2 <= f)%nat -> croom L (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) ->
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - BPUTS_STACK -> mbio_rep m LBall L K BI meth len max 0 -> len + n < 2^30 ->
    cown LBall L pl LB 256 256 -> ~ mbio_T K pl -> length bs = 256%nat -> rw_cells usegs m LB [CB 256 bs] ->
    0 <= n <= 255 -> nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0) -> (forall i, (i < Z.to_nat n)%nat -> nth_error bs i <> Some (Z_to_bv 8 0)) ->
    a0 = wz BI -> a1 = wz LB ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_PUTS) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (mbio_T K) [] 2
             (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) (bio_puts_res K BI meth len max n LBall L)).

  (* [comment removed for export] *)
  Definition bio_write0_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (n lo B : Z),
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - 16 -> a2 = wz n -> - 2 ^ 31 <= n <= 0 ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_WRITE) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun _ => False) [] 0 0 0 0
         (fun v LBall' L' _ => v = wz 0 /\ LBall' = LBall /\ L' = L)).
  Definition bio_write_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (BI meth len max IN n lo B : Z)
           (src : list byte),
    (2 <= f)%nat -> croom L (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) ->
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - BWRITE_STACK -> mbio_rep m LBall L K BI meth len max 0 -> len + n < 2^30 ->
    0 < n < 2^31 -> bytes_at usegs m IN src -> length src = Z.to_nat n -> src_loc LBall (mbio_T K) (bv_unsigned sp) IN n -> bv_unsigned sp mod 16 = 0 ->
    a0 = wz BI -> a1 = wz IN -> a2 = wz n ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_WRITE) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (mbio_T K) [] 2
             (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) (bio_puts_res K BI meth len max n LBall L)).

  (* [comment removed for export] *)
  Definition bio_ctrl_ptr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (BI meth len max off lo B : Z)
           (qs : list cell) (old : word),
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - BCTRL_STACK -> mbio_rep m LBall L K BI meth len max off ->
    rw_cells usegs m (bv_unsigned sp) qs -> Z.of_nat (cells_size qs) = 88 -> rw_cells usegs m (bv_unsigned sp + 88) [C8 old] -> bv_unsigned sp + 96 <= B -> bv_unsigned sp mod 16 = 0 ->
    a0 = wz BI -> a1 = wz 115 -> a2 = wz 0 -> a3 = wz (bv_unsigned sp + 88) ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_CTRL) fc None m (seg_rom usegs))
      (cpostx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (mbio_T K) [] (bv_unsigned sp + 96) 0 0 0 0
         (fun v LBall' L' m' => exists BM, v = wz 1 /\ LBall' = LBall /\ L' = L /\ rw_cells usegs m' (bv_unsigned sp) qs /\ rw_cells usegs m' (bv_unsigned sp + 88) [C8 (wz BM)]
              /\ mbio_repx m' LBall L K BI BM (wz (len - off)) meth (len - off) max 0)).

  (* [comment removed for export] *)
  Definition bio_ctrl_info_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (BI meth len max off lo B : Z),
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - BCTRL_STACK -> mbio_rep m LBall L K BI meth len max off ->
    a0 = wz BI -> a1 = wz 3 -> a2 = wz 0 -> a3 = wz 0 ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_CTRL) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun _ => False) [] 0 0 0 0
         (fun v LBall' L' m' => v = wz (len - off) /\ LBall' = LBall /\ L' = L /\ mbio_rep m' LBall L K BI meth len max off)).

  (* [comment removed for export] *)
  Definition bio_read_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (po : bptr)
           (BI BM meth len max off OUT no n lo B : Z) (blw : word) (ojunk : list byte),
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - BREAD_STACK -> mbio_repx m LBall L K BI BM blw meth len max off ->
    1 <= n <= len - off -> cown LBall L po OUT no no -> ~ mbio_T K po -> n <= no -> length ojunk = Z.to_nat no -> rw_cells usegs m OUT [CB (Z.to_nat no) ojunk] -> bv_unsigned sp mod 16 = 0 ->
    a0 = wz BI -> a1 = wz OUT -> a2 = wz n ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_READ) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun q => mbio_T K q \/ q = po) [] 0 0 0 0
         (fun v LBall' L' m' => exists ojunk' : list byte, v = wz n /\ LBall' = LBall /\ L' = L /\ mbio_repx m' LBall L K BI BM blw meth len max (off + n)
              /\ length ojunk' = Z.to_nat no /\ rw_cells usegs m' OUT [CB (Z.to_nat no) ojunk'])).

  (* [comment removed for export] *)
  Definition ECTX : Z := 92.
  Definition evp_ctx_new_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (lo B : Z),
    (1 <= f)%nat -> croom L 1 0 0 -> cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - (16 + CZ_STACK) ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_EVP_CTX_NEW) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun _ => False) [] 1 1 0 0 (cs_zalloc_res ECTX LBall L)).
  Definition evp_ctx_free_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (p : bptr) (A lo B : Z),
    (1 <= f)%nat -> cown LBall L p A ECTX ECTX -> cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - (16 + CF_STACK) -> a0 = wz A ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_EVP_CTX_FREE) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (eq p) [] 1 (-1) 0 0 (pem_free_res p ECTX LBall L)).
  Definition evp_ctx_free_null_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (lo B : Z),
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - (16 + CF_STACK) -> a0 = wz 0 ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_EVP_CTX_FREE) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun _ => False) [] 0 0 0 0
         (fun _ LBall' L' _ => LBall' = LBall /\ L' = L)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PEMR_STACK : Z := 208 + BPUTS_STACK.

  (* [comment removed for export] *)
  Definition pem_out (ret : Z) (m : mem) (LBall : list block) (L : @clist bptr) (PN PH PD PL : Z) (news : list block) : Prop :=
    (ret = 0 /\ news = [] /\ rw_cells usegs m PN [C8 (wz 0)] /\ rw_cells usegs m PH [C8 (wz 0)] /\ rw_cells usegs m PD [C8 (wz 0)] /\ (exists lw, rw_cells usegs m PL [C8 lw]))
    \/ (ret = 1 /\ exists (qn qh qd : bptr) (NM HD DT nn nh dlen : Z) (bn bh bd : list byte),
           news = [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]
        /\ cown LBall L qn NM nn nn /\ cown LBall L qh HD nh nh /\ cown LBall L qd DT dlen dlen /\ 1 <= nn <= 255 /\ 1 <= nh < 2^31 /\ 1 <= dlen < 2^31
        /\ rw_cells usegs m PN [C8 (wz NM)] /\ rw_cells usegs m PH [C8 (wz HD)] /\ rw_cells usegs m PD [C8 (wz DT)] /\ rw_cells usegs m PL [C8 (wz dlen)]
        /\ length bn = Z.to_nat nn /\ rw_cells usegs m NM [CB (Z.to_nat nn) bn] /\ In (Z_to_bv 8 0) bn
        /\ length bh = Z.to_nat nh /\ rw_cells usegs m HD [CB (Z.to_nat nh) bh] /\ nth_error bh (Z.to_nat (nh - 1)) = Some (Z_to_bv 8 0)
        /\ length bd = Z.to_nat dlen /\ rw_cells usegs m DT [CB (Z.to_nat dlen) bd]).

  (* [comment removed for export] *)
  Definition strs_inL (L : @clist bptr) (strs : list block) : Prop := Forall (fun b => In (blk_id b, blk_size b) L /\ blk_size b <= 64) strs.

  (* [comment removed for export] *)
  Definition news_sz (news : list block) : Z := fold_right (fun b acc => blk_size b + acc) 0 news.

  Definition pem_read_res (K : mbk) (BI meth blen bmax boff PL E : Z) (LBL LBall : list block) (L : @clist bptr)
      : word -> list block -> @clist bptr -> mem -> Prop :=
    fun v LBall' L' m' => exists (ret boff' top bot : Z) (strs news : list block),
         v = wz ret /\ boff <= boff' <= blen /\ mbio_rep m' LBall' L' K BI meth blen bmax boff'
      /\ libenv m' LBL E /\ errst_live E top bot strs m' /\ (length strs <= 2)%nat /\ strs_inL L' strs
      /\ List.NoDup (map blk_id (strs ++ news)) /\ news_sz news <= 2 * (boff' - boff) + 256
      /\ pem_out ret m' LBall' L' (PL + 24) (PL + 16) (PL + 8) PL news
      /\ (forall b, In b LBall' <-> (In b LBall \/ In b (strs ++ news))) /\ (forall b, In b (strs ++ news) -> ~ In (blk_id b) (map blk_id LBall))
      /\ (forall q nm, In (q, nm) L -> In (q, nm) L').

  (* [comment removed for export] *)
  Definition pem_read_bio_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 LBL : list block) (L : @clist bptr) (f : nat) (K : mbk) (pe : bptr)
           (BI meth blen bmax boff PL flags E enm lo B : Z) (on oh od ol : word),
    (Z.to_nat (40 + 2 * (blen - boff)) <= f)%nat ->
    croom L 16 8 (6 * (blen - boff) + 4 * (256 + 8192) + 65536) ->
    cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - PEMR_STACK -> libenv m LBL E -> incl_blocks LBL LBall -> (forall b, In b LBL -> ~ (mbio_T K (blk_id b) \/ blk_id b = pe)) ->
    (* [comment removed for export] *)
    cown LBall L pe E 904 enm ->
    (* [comment removed for export] *)
    ~ In pe (mbio_blocks K) ->
    errst_at_rest E [] m ->
    mbio_rep m LBall L K BI meth blen bmax boff -> blen < 2^26 -> PL = bv_unsigned sp -> PL + 32 <= B -> PL mod 16 = 0 ->
    rw_cells usegs m PL [C8 ol; C8 od; C8 oh; C8 on] ->
    a0 = wz BI -> a1 = wz (PL + 24) -> a2 = wz (PL + 16) -> a3 = wz (PL + 8) -> a4 = wz PL -> a5 = wz flags -> 0 <= flags < 256 ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_PEM_READ_BIO) fc None m (seg_rom usegs))
      (cpostx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun q => mbio_T K q \/ q = pe) [] (PL + 32)
             (Z.to_nat (40 + 2 * (blen - boff))) 16 8 (6 * (blen - boff) + 4 * (256 + 8192) + 65536)
             (pem_read_res K BI meth blen bmax boff PL E LBL LBall L)).

  (* [comment removed for export] *)
  Definition pem_read_bio_deps : Prop :=
    pem_malloc_stmt -> pem_malloc0_stmt -> pem_free_stmt -> pem_free_null_stmt -> sanitize_line_stmt ->
    err_new_rest_stmt -> err_set_debug_stmt -> err_set_error_stmt ->
    bio_new_mem_stmt -> bio_free_mem_stmt -> bio_gets_stmt -> bio_puts_stmt -> bio_ctrl_ptr_stmt -> bio_ctrl_info_stmt -> bio_read_stmt ->
    evp_ctx_new_stmt -> evp_ctx_free_stmt -> evp_ctx_free_null_stmt ->
    pem_read_bio_stmt.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable C : cli_sig.
  Variable REST : mem -> list block -> Prop.
  Variable rest_fp : list block -> Z -> Prop.
  Definition cli_open : Prop := forall m CLB, CLI C m CLB -> exists (pe : bptr) (E : Z) (LBL : list block), In (pe, E, 904) CLB /\ ~ In pe (map blk_id LBL) /\ incl_blocks LBL CLB
      /\ libenv m LBL E /\ errst_at_rest E [] m /\ REST m CLB.
  Definition cli_close : Prop := forall m m' CLB (pe : bptr) (E : Z) (LBL : list block),
    In (pe, E, 904) CLB -> incl_blocks LBL CLB -> REST m CLB -> agree_on (rest_fp CLB) m m' -> libenv m' LBL E -> errst_at_rest E [] m' -> CLI C m' CLB.
  Definition fuzz_one_deps : Prop :=
    cli_open -> cli_close ->
    bio_new_mem_stmt -> bio_write_stmt -> bio_write0_stmt -> pem_read_bio_stmt -> bio_free_mem_stmt -> err_clear_steady_stmt ->
    crypto_free_stmt -> crypto_secure_free_stmt -> rfuzz_one_stmt C.
End CallIface.
End WithCeiling0.
