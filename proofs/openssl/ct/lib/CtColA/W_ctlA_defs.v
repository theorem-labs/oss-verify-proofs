(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA Fr_asn1_check_tlen W_check_tlenA W_get_object_closedA W_err_newA W_err_set_debugA W_err_vsetA ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import CtSizes CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require W_check_tlen_gen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_check_tlen_genA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctl_xt (ot : option Z) : Z := match ot with Some t => t | None => -1 end.
Definition ctl_tlc (TLCo : option Z) : Z := match TLCo with Some a => a | None => 0 end.

Definition ctl_frameA (j0 j8 j16 j24 j32 j40 : list byte) (f PIC PPC len : Z) (ot : option Z) (j128 j136 : list byte) (gg : nat) (junk : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32;
   CB 8 j40; C8 (Z_to_bv 64 (Z.shiftr PPC 3 + SHB)); C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 PIC); C8 (Z_to_bv 64 (PIC + 2)); C8 (Z_to_bv 64 (PIC + 1)); C8 (Z_to_bv 64 PPC);
   C8 (Z_to_bv 64 (ctl_xt ot)); C8 (Z_to_bv 64 len); CB 8 j128; CB 8 j136; C8 (Z_to_bv 64 f); CB gg junk].

(* [comment removed for export] *)
Definition ctl_frame0A (j0 j8 j16 : list byte) (c24 c32 c40 : cell) (f PIC PPC len : Z) (ot : option Z) (j128 j136 : list byte) (gg : nat) (junk : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; c24; c32;
   c40; C8 (Z_to_bv 64 (Z.shiftr PPC 3 + SHB)); C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 PIC); C8 (Z_to_bv 64 (PIC + 2)); C8 (Z_to_bv 64 (PIC + 1)); C8 (Z_to_bv 64 PPC);
   C8 (Z_to_bv 64 (ctl_xt ot)); C8 (Z_to_bv 64 len); CB 8 j128; CB 8 j136; C8 (Z_to_bv 64 f); CB gg junk].

Lemma ctl_frame0A_cb : forall m spa j0 j8 j16 c24 c32 c40 f PIC PPC len ot j128 j136 gg junk,
  csize c24 = 8%nat -> csize c32 = 8%nat -> csize c40 = 8%nat ->
  rw_cells ctasegs m spa (ctl_frame0A j0 j8 j16 c24 c32 c40 f PIC PPC len ot j128 j136 gg junk) ->
  rw_cells ctasegs m spa (ctl_frameA j0 j8 j16 (cbytes c24) (cbytes c32) (cbytes c40) f PIC PPC len ot j128 j136 gg junk).
Proof.
  intros until junk. intros E24 E32 E40 H. apply (rw_cells_cb_first m spa _ 6) in H. cbn [cb_first csize cbytes ctl_frame0A] in H.
  rewrite E24, E32, E40 in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma land_le_lA : forall x y, 0 <= x -> Z.land x y <= x.
Proof.
  intros x y Hx.
  assert (D0 : Z.land (Z.ldiff x y) (Z.land x y) = 0).
  { rewrite (Z.land_comm x y), Z.land_assoc, Z.land_ldiff. apply Z.land_0_l. }
  pose proof (Z.add_nocarry_lxor _ _ D0) as E1. rewrite (Z.lxor_lor _ _ D0), Z.lor_ldiff_and in E1.
  assert (H1 : 0 <= Z.ldiff x y) by (apply Z.ldiff_nonneg; left; exact Hx). lia.
Qed.

Lemma ctl_frameA_size : forall j0 j8 j16 j24 j32 j40 f PIC PPC len ot j128 j136 gg junk,
  Z.of_nat (cells_size (ctl_frameA j0 j8 j16 j24 j32 j40 f PIC PPC len ot j128 j136 gg junk)) = 152 + Z.of_nat gg.
Proof. intros. unfold ctl_frameA. cbn [cells_size csize]. lia. Qed.

(* [comment removed for export] *)
Definition ctl_XX (PIC PPC : Z) (TLCo : option Z) : list (Z * Z) :=
  [(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)].

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctl_factsA
    (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m3 : mem) (Σ Σ1 : rts RT) (OW LB K : list block) (E : ap_env) (lo : Z) (ras : list Z)
    (D : Z) (d : list Z) (op len PIC PPC : Z) (TLCo ot : option Z)
    (f spa : Z) (gg : nat) (junk gj : list byte) (bd bt : block) : Prop :=
  (0 <= bv_unsigned sp < 2 ^ 64)
  /\ (SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP)
  /\ ACEIL <= lo /\ lo + 66352 <= bv_unsigned sp /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0 /\ 0 <= lo
  /\ 0 < f /\ f mod 64 = 0 /\ f + 128 <= ACEIL /\ SEGTOP_A <= f /\ (f + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
  /\ spa mod 32 = 0 /\ bv_unsigned sp - 272 <= spa /\ spa <= bv_unsigned sp - 256
  /\ bv_unsigned (Z_to_bv 64 spa) = spa /\ bv_unsigned (Z_to_bv 64 f) = f
  /\ (forall b, In b LB -> off_fr f 1 b)
  /\ Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 26
  /\ In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd
  /\ 0 <= op /\ 0 < len /\ op + len <= zlength d
  /\ match ot with Some t => 0 <= t < 2 ^ 31 | None => True end
  /\ bv_unsigned sp <= PIC /\ PIC + 10 <= USTACK_TOP /\ bv_unsigned sp <= PPC /\ PPC + 8 <= USTACK_TOP
  /\ (PPC + 8 <= PIC \/ PIC + 10 <= PPC) /\ (PIC + 2) mod 8 = 0 /\ PPC mod 8 = 0
  /\ match TLCo with Some a => In bt LB /\ blk_addr bt <= a /\ a + 32 <= blk_addr bt + blk_size bt /\ a mod 8 = 0 | None => True end
  /\ Z.of_nat (length FR) + 6 <= Z.of_nat FRAMES_MAX
  /\ 27 <= rt_credit RT Σ /\ rt_credit RT Σ1 = rt_credit RT Σ - 1
  /\ Z.of_nat gg = bv_unsigned sp - spa - 168 /\ junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
  /\ (forall b, In b K -> In b OW) /\ (forall b, In b K -> ~ In (blk_id b) (env_ids E)) /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3
  /\ uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras /\ uk_ctx CHECK_TLEN_A (bv_unsigned ra :: ras) /\ ras <> nil.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctl_memA
    (ra sp s0 : word) (m : mem) (Σ : rts RT) (LB K : list block) (E : ap_env) (lo : Z) (ras : list Z) (PIC PPC : Z) (TLCo : option Z)
    (f spa : Z) (qp ql qt qc : bptr)
    (ma : mem) (Σ4 : rts RT) (st4 : ap_st bptr) (OW4 : list block) (bo4 : Z * Z) (spent : Z) (frame : list cell) : Prop :=
  @ap_preA (push AR f 1) Σ4 st4 ma OW4 (actl_pbs f qp ql qt qc ++ LB) E bo4 (Z_to_bv 64 spa) lo 0 0 0
  /\ blocks_kept K st4 OW4 m ma
  /\ agree_on (ax_client LB (bv_unsigned sp) (ctl_XX PIC PPC TLCo ++ LIBW_A)) m ma
  /\ rt_credit RT Σ - spent <= rt_credit RT Σ4
  /\ rw_cells ctasegs ma spa frame
  /\ rw_cells ctasegs ma (bv_unsigned sp + -16) [C8 s0; C8 ra].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctl_tlcA (TLCo : option Z) (m' : mem) : Prop :=
  match TLCo with Some a => exists vb j, rw_cells ctasegs m' a [C1 vb; CB 31 j] | None => True end.

(* [comment removed for export] *)
Definition ctl_rpostA
    (ra sp gp s0 : word) (m : mem) (Σ : rts RT) (LB K : list block) (E : ap_env) (lo : Z) (ras : list Z) (PIC PPC : Z) (TLCo : option Z)
    (f spa : Z) (qp ql qt qc : bptr) (spent : Z) (frame : list cell) (x20 x24 x25 x26 : word) (cpic : list cell) (pp : Z)
    (r : unit * ap_st bptr) (Σ7 : rts RT) : machine_state -> Prop :=
  fun ms7 => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F7 : bvmap 5 word) (fc7 : bv 32) m7 OW7 bo7,
    ms7 = MS (mkR (Z_to_bv 64 0x242bd4) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) x24 x25 x26 (Z_to_bv 64 SHB) t3 t4 t5 t6)
             F7 (Z_to_bv 64 0x242bd4) fc7 None m7 (seg_rom ctasegs)
    /\ ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc m7 Σ7 (snd r) OW7 bo7 spent frame
    /\ rw_cells ctasegs m7 PIC cpic /\ rw_cells ctasegs m7 PPC [C8 (Z_to_bv 64 pp)] /\ ctl_tlcA TLCo m7.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lib_addr_lowA : forall Σ OW L m a, AHEAP Σ OW L m -> lib_addr OW a -> a < ACEIL.
Proof.
  intros Σ OW L m a HEAP [HS|(b & Hb & Hr)].
  - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R4 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma lib_addr_apartA : forall Σ OW L m b a, AHEAP Σ OW L m -> In b L -> blk_addr b <= a < blk_addr b + blk_size b -> lib_addr OW a -> False.
Proof.
  intros Σ OW L m b a HEAP Hb Hr [HS|(b' & Hb' & Hr')].
  - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA.
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & _ & R5). lia.
  - pose proof (AH_nodup _ _ _ _ HEAP) as ND. destruct b' as [[q A] n].
    pose proof (ids_disj OW L q A n ND Hb' b Hb) as NE.
    pose proof (AH_disjoint_gen _ _ _ _ b (q, A, n) HEAP (in_or_app _ _ _ (or_intror Hb)) (in_or_app _ _ _ (or_introl Hb')) NE) as DJ.
    cbn [blk_addr blk_size fst snd] in Hr', DJ. lia.
Qed.

(* [comment removed for export] *)
Lemma client_static_lowA : forall a, client_static a -> a < SEGTOP_A.
Proof.
  intros a [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A.
  destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia.
Qed.

(* [comment removed for export] *)
Lemma blocks_kept_munchA : forall K (st' : ap_st bptr) (OW' : list block) m m1 m2 W,
  blocks_kept K st' OW' m m1 -> munch W m1 m2 -> (forall a, lib_addr OW' a -> outside W a) -> blocks_kept K st' OW' m m2.
Proof.
  intros K st' OW' m m1 m2 W (B1 & B2 & B3) MU LOUT. split; [exact B1|]. split; [exact B2|].
  intros a Ha Hin. rewrite <- (B3 a Ha Hin). apply (agree_on_of_munch_nw _ _ _ MU a Ha). apply LOUT. right. eapply in_block_mono; [exact B1| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma blocks_kept_transA : forall K (st1 st2 : ap_st bptr) (OW1 OW2 : list block) m m1 m2,
  blocks_kept K st1 OW1 m m1 -> blocks_kept K st2 OW2 m1 m2 -> blocks_kept K st2 OW2 m m2.
Proof.
  intros K st1 st2 OW1 OW2 m m1 m2 (A1 & A2 & A3) (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
  intros a Ha Hin. rewrite (B3 a Ha Hin). exact (A3 a Ha Hin).
Qed.

(* [comment removed for export] *)
Lemma ap_preA_restockA : forall Σ' (st' : ap_st bptr) m' OW' L E bo' (spw : word) lo stack cost frames,
  ap_preA Σ' st' m' OW' L E bo' spw lo 0 0 0 -> lo <= bv_unsigned spw - stack -> 0 <= cost <= rt_credit RT Σ' ->
  0 <= frames -> Z.of_nat (length FR) + frames <= Z.of_nat FRAMES_MAX ->
  ap_preA Σ' st' m' OW' L E bo' spw lo stack cost frames.
Proof.
  intros until frames. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) H1 H2 H3 H4.
  unfold ap_preA. repeat (split; [first [assumption | lia]|]). lia.
Qed.

(* [comment removed for export] *)
Lemma ctl_memA_reframe : forall (ra sp s0 : word) m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc ma Σ4 (st4 : ap_st bptr) OW4 bo4 spent frame frame',
  ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc ma Σ4 st4 OW4 bo4 spent frame ->
  (rw_cells ctasegs ma spa frame -> rw_cells ctasegs ma spa frame') ->
  ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc ma Σ4 st4 OW4 bo4 spent frame'.
Proof.
  intros until frame'. intros (PRE4 & KEPT4 & AX4 & CRED4 & FRL & FRH) HF.
  split; [exact PRE4|]. split; [exact KEPT4|]. split; [exact AX4|]. split; [exact CRED4|]. split; [exact (HF FRL)| exact FRH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ctl_memA_munch : forall (ra sp s0 : word) m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc ma mb Σ4 (st4 : ap_st bptr) OW4 bo4 spent frame W,
  ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc ma Σ4 st4 OW4 bo4 spent frame ->
  munch W ma mb -> wmono ctasegs ma mb -> mem_inv ctasegs mb -> stk ctasegs mb lo spa ->
  Forall (@aclient_write_ok (push AR f 1) (OW4 ++ (actl_pbs f qp ql qt qc ++ LB))) W ->
  (forall a, lib_addr OW4 a -> outside W a) ->
  (forall a, ax_client LB (bv_unsigned sp) (ctl_XX PIC PPC TLCo ++ LIBW_A) a -> outside W a) ->
  (forall a, spa <= a < spa + Z.of_nat (cells_size frame) -> outside W a) ->
  (forall a, bv_unsigned sp - 16 <= a < bv_unsigned sp -> outside W a) ->
  bv_unsigned (Z_to_bv 64 spa) = spa ->
  ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc mb Σ4 st4 OW4 bo4 spent frame.
Proof.
  intros until W. intros (PRE4 & KEPT4 & AX4 & CRED4 & FRL & FRH) MU WM MI ST WOK LOUT XOUT FOUT SOUT ESPA.
  pose proof PRE4 as (HEAP4 & _).
  assert (AGL : agree_on (lib_addr OW4) ma mb) by (eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]; exact LOUT).
  assert (HEAPb : @BnHeapA.AHEAP (push AR f 1) Σ4 OW4 (actl_pbs f qp ql qt qc ++ LB) mb) by (eapply (@AH_frame (push AR f 1)); [exact HEAP4| exact MU| exact WM| exact WOK]).
  split; [eapply (@ap_preA_memA (push AR f 1)); [exact PRE4| exact HEAPb| exact AGL| rewrite ESPA; exact ST| exact MI]|].
  split; [exact (blocks_kept_munchA K st4 OW4 m ma mb W KEPT4 MU LOUT)|].
  split; [eapply agree_on_trans; [exact AX4| eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)| exact XOUT]]|].
  split; [exact CRED4|].
  split; [eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU)| exact FRL| intros a Ha; apply FOUT; exact Ha]|].
  eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU)| exact FRH| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply SOUT; lia].
Qed.

End WithRT.

(* [comment removed for export] *)
Ltac ctl_facts F :=
  pose proof F as (SPR & CN & CEIL & LOSP & TOP & AL16 & LO0 & G1 & G2 & G3 & G4 & G5 & SPA32 & SPAL & SPAH & ESPA & Ef & OFFLB & PF & D0 & D63 & D26 & HBD & PA1 & PA2
                   & OP0 & TL0 & OPT & OT & PIClo & PIChi & PPClo & PPChi & DJ & AL2 & AL1 & TB & FRMX & CRED & CR1 & GSZ & SAVJ & KOW & KIDE & AGF & UW & CTX & RNE);
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CN; unfold SEGTOP_A in G4.
