(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.punycode.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.punycode.lib.MallocP Require RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Layout Exit Printf_wfile F_memcpy F_memset Fz_iface Drv_kit.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma LH_block_range : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof. intros. eapply RMalloc_ifaceP.RHEAP_block_range_proof; eauto. Qed.

Lemma LH_nodup : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof. intros. eapply RMalloc_ifaceP.RHEAP_blocks_nodup_proof; eauto. Qed.

Lemma LH_disjoint : forall s LB m b1 b2,
  RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof. intros. eapply RMalloc_ifaceP.RHEAP_blocks_disjoint_proof; eauto. Qed.

(* [comment removed for export] *)
Lemma LH_frame : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono psegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Proof. intros. eapply RMalloc_ifaceP.RHEAP_frame_proof; eauto. Qed.

Lemma W_ok_stack : forall LB lo hi, alloc_ceiling <= lo -> rclient_write_ok LB (lo, hi).
Proof. intros LB lo hi H. left. cbn. exact H. Qed.

Lemma W_ok_block : forall LB b lo hi, In b LB -> blk_addr b <= lo -> hi <= blk_addr b + blk_size b ->
  rclient_write_ok LB (lo, hi).
Proof. intros LB b lo hi Hb H1 H2. right; right. exists b. cbn. auto. Qed.

(* [comment removed for export] *)
Lemma W_ok_latch : forall LB, rclient_write_ok LB (LX_FLAGS, LX_FLAGS + 1).
Proof.
  intros LB. right; left. cbn [fst snd]. unfold LX_FLAGS, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma outside_of_X : forall X a, ~ rin_ivs X a -> outside X a.
Proof.
  intros X a. induction X as [|[lo hi] X IH]; intros H; cbn in *; [exact I|].
  split; [lia|]. apply IH. tauto.
Qed.

(* [comment removed for export] *)
Lemma lx_pres_of_munch : forall LB SP X W m m',
  munch W m m' -> wmono psegs m m' ->
  (forall a, 0 <= a < 2^64 -> lx_client LB SP X a -> outside W a) ->
  lx_pres LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM HW a Ha Hc. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. apply HW; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_post_evt : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl psegs (at_node psegs) t Q ms -> (forall r ms', Q r ms' -> evt psegs (Q' r) ms') ->
  impl psegs (at_node psegs) t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma implM_post_evt : forall {A} (c : M PState A) s Q Q' ms,
  implM psegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt psegs (Q' a s') ms') ->
  implM psegs c s Q' ms.
Proof.
  intros A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

(* [comment removed for export] *)
Lemma heap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono psegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HW a Ha Hc. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. apply HW; assumption.
Qed.

Lemma rclient_addr_cases : forall LB SP a,
  rclient_addr LB SP a -> SP <= a \/ (0x27b000 <= a < 0x30e000 /\ ~ ralloc_static a) \/ (exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b).
Proof. intros LB SP a [H|[H|H]]; [left| right; left| right; right]; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LX_ERRNO : Z := RATP - 164.

Definition malloc_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q
    /\ rw_cells psegs m' LX_ERRNO [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells psegs m' A [CB (Z.to_nat n) junk]
       end.

Lemma malloc_callZ : rmalloc_stmt ->
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> q <= B ->
  stk psegs m lo q -> alloc_ceiling <= lo -> lo <= q - RMALLOC_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] ->
  mem_inv psegs m -> 0 <= q < 2^64 -> 0 <= n < 2^32 ->
  implM psegs (raw_malloc n) s
        (malloc_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom psegs)).
Proof.
  intros HM. intros until errv. intros HEAP AUX QB ST CEIL LO ERR MI Hq Hn.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Et : bv_unsigned (Z_to_bv 64 RATP) + -164 = LX_ERRNO) by (unfold LX_ERRNO, RATP; rewrite unsigned_lit by lia; lia).
  eapply implM_mono.
  { eapply HM with (B := B) (lo := lo); rewrite ?Eq, ?Et; try eassumption; try reflexivity; try lia. }
  cbv beta. intros r s' ms' PO. unfold rmalloc_post in PO. unfold malloc_postZ. rewrite !Eq, !Et in PO.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & errv' & E & REST).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', errv'. split; [exact E|].
  destruct REST as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [assumption|]).
  destruct r as [p|]; [| exact A8].
  destruct A8 as (A & junk & B1 & B2 & B3 & B4 & _). exists A, junk. auto.
Qed.

Definition free_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q
    /\ rw_cells psegs m' LX_ERRNO [C4 errv]
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove p LB) m'.

Lemma free_callZ : rfree_stmt ->
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (q A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> q <= B ->
  stk psegs m lo q -> alloc_ceiling <= lo -> lo <= q - RFREE_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] ->
  mem_inv psegs m -> 0 <= q < 2^64 ->
  implM psegs (raw_free p) s
        (free_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom psegs)).
Proof.
  intros HF. intros until errv. intros HEAP IN AUX QB ST CEIL LO ERR MI Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Et : bv_unsigned (Z_to_bv 64 RATP) + -164 = LX_ERRNO) by (unfold LX_ERRNO, RATP; rewrite unsigned_lit by lia; lia).
  eapply implM_mono.
  { eapply HF with (B := B) (lo := lo); rewrite ?Eq, ?Et; try eassumption; try reflexivity; try lia. }
  cbv beta. intros r s' ms' PO. unfold rfree_post in PO. unfold free_postZ. rewrite !Eq, !Et in PO. exact PO.
Qed.

(* [comment removed for export] *)
Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at psegs m' Src src.
Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at psegs m Src src -> length src = Z.to_nat N -> rw_cells psegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv psegs m ->
  evt psegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x276444) fc None m (seg_rom psegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memcpy.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold F_memcpy.memcpy_post, memcpy_postZ in *. rewrite ED, ES, EN in P. exact P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lxs_addr_lt : forall a, lxs_addr a -> 0x27b000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof.
  intros a Ha. unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP,
    LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in *. lia.
Qed.
Lemma flags_addr_lt : forall a, flags_addr a -> 0x27b000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof. intros a Ha. unfold flags_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP, LX_FLAGS in *. lia. Qed.
Lemma stderr_addr_lt : forall a, stderr_addr a -> 0x27b000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof. intros a Ha. unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP in *. lia. Qed.
Lemma ssp_addr_lt : forall a, ssp_addr a -> 0x27b000 <= a < GLOBALS_TOP.
Proof. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard, GLOBALS_TOP in *. lia. Qed.

(* [comment removed for export] *)
Lemma statics_heap : forall LB SP m m' ,
  rheap_pres LB SP m m' ->
  (lx_statics m -> lx_statics m') /\ (lx_flags0 m -> lx_flags0 m') /\ (stderr_wfile m -> stderr_wfile m').
Proof.
  intros LB SP m m' HP. pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
  split; [|split].
  - intros H. eapply lx_statics_agree; [exact AG| |exact H]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. right; left. unfold GLOBALS_TOP in R1. split; [lia| exact R2].
  - intros H. eapply lx_flags_agree; [exact AG| |exact H]. intros a Ha. pose proof (flags_addr_lt a Ha) as [R1 R2]. right; left. unfold GLOBALS_TOP in R1. split; [lia| exact R2].
  - intros H. eapply stderr_wfile_agree; [exact AG| |exact H]. intros a Ha. pose proof (stderr_addr_lt a Ha) as [R1 R2]. right; left. unfold GLOBALS_TOP in R1. split; [lia| exact R2].
Qed.

(* [comment removed for export] *)
Lemma statics_munch : forall W m m' c,
  munch W m m' -> wmono psegs m m' ->
  (forall a, 0x27b000 <= a < GLOBALS_TOP -> ~ flags_addr a -> outside W a) ->
  (lx_statics m -> lx_statics m') /\ (stderr_wfile m -> stderr_wfile m') /\ (ssp_cells m c -> ssp_cells m' c).
Proof.
  intros W m m' c MU WM HW. pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  split; [|split].
  - intros H. eapply lx_statics_agree; [exact AG| |exact H]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. apply HW; [exact R1|].
    unfold lxs_addr, flags_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_FLAGS in *. lia.
  - intros H. eapply stderr_wfile_agree; [exact AG| |exact H]. intros a Ha. pose proof (stderr_addr_lt a Ha) as [R1 R2]. apply HW; [exact R1|].
    unfold stderr_addr, flags_addr, LX_FLAGS in *. lia.
  - intros H. eapply ssp_cells_agree; [exact AG| |exact H]. intros a Ha. pose proof (ssp_addr_lt a Ha) as R1. apply HW; [exact R1|].
    unfold ssp_addr, got_ssp, ssp_guard, flags_addr, LX_FLAGS in *. lia.
Qed.

(* [comment removed for export] *)
Lemma payload_ok_agree : forall P m m' LB D d,
  agree_on P m m' -> payload_ok m LB D d ->
  (forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> P a) ->
  payload_ok m' LB D d.
Proof.
  intros P m m' LB D d AG (BY & HF & HD & HD63 & HD31 & HB) HP.
  split; [| split; [exact HF| split; [exact HD| split; [exact HD63| split; [exact HD31| exact HB]]]]].
  destruct HB as [->|(b & Hb & Hb1 & Hb2)].
  - destruct BY as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
  - eapply bytes_at_agree; [exact AG| exact BY|]. intros a Ha. rewrite to_bytes_length in Ha. unfold zlength in Hb2.
    apply (HP b); [exact Hb| lia].
Qed.

Lemma payload_ok_heap : forall LB SP m m' D d,
  rheap_pres LB SP m m' -> payload_ok m LB D d -> payload_ok m' LB D d.
Proof.
  intros LB SP m m' D d HP PL. eapply payload_ok_agree; [apply agree_of_heap_pres; exact HP| exact PL|].
  intros b a Hb Ha. right; right. exists b. auto.
Qed.
End WithCeiling0.
