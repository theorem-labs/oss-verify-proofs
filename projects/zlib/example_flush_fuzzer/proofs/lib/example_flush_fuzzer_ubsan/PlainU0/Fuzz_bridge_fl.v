(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Exec MonadX CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import DrvAgree Printf_fmts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface FlLibStmtU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import PImg StdioFiles F_syscalls Stdio_iface F_printf_iface F_calloc.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface U2Kit FlKit FlSeg1 FlSeg2 FlSeg3 FlCall FlLinks.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require RMalloc_ifaceP RDriver_facts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim Malloc Monad CMonad CMonadX Stdio Prog ProgC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require HarnessC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require ZIface DeflateState Deflate InflateState Inflate InflateRc InflateSync HarnessKit HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac bl_vars_in_goal t :=
  lazymatch t with
  | ?a \/ ?b => bl_vars_in_goal a; bl_vars_in_goal b
  | ?a /\ ?b => bl_vars_in_goal a; bl_vars_in_goal b
  | (?a <= ?b)%Z => bl_vars_in_goal a; bl_vars_in_goal b
  | (?a < ?b)%Z => bl_vars_in_goal a; bl_vars_in_goal b
  | (?a + ?b)%Z => bl_vars_in_goal a; bl_vars_in_goal b
  | (?a - ?b)%Z => bl_vars_in_goal a; bl_vars_in_goal b
  | (?a * ?b)%Z => bl_vars_in_goal a; bl_vars_in_goal b
  | ?x => tryif is_var x then (lazymatch goal with |- context [x] => idtac end) else idtac
  end.
Ltac bl_prune :=
  repeat match goal with
         | H : ?A \/ ?B |- _ => tryif bl_vars_in_goal (A \/ B) then fail else clear H
         end.
Ltac blia := first [ solve [bl_prune; lia] | lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* kitfix4 alias stage: Module OX := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface expanded *)

Lemma outside_Forall : forall (P : Z * Z -> Prop) (W : list (Z * Z)) x,
  Forall P W -> (forall iv, P iv -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  intros P W x HF HP. induction HF as [|[a b] W Hiv _ IH]; cbn; [exact I|]. split; [exact (HP _ Hiv)| exact IH].
Qed.

Lemma nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; cbn; intros l2 x ND H1 H2; [exact H1|]. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [->|H1]; [apply NI; apply in_or_app; right; exact H2| exact (IH l2 x ND' H1 H2)].
Qed.

Lemma NoDup_app_l : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  induction l1 as [|a l1 IH]; cbn; intros l2 ND; [constructor|]. inversion ND as [|? ? NI ND']; subst.
  constructor; [intros HI; apply NI; apply in_or_app; left; exact HI| exact (IH l2 ND')].
Qed.

Lemma skipn_repeat : forall {A} (x : A) n k, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x n k. revert n. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

Lemma firstn_repeat : forall {A} (x : A) n k, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x n k. revert n. induction k as [|k IH]; intros [|n] Hk; cbn; try reflexivity; [lia|]. f_equal. apply IH. lia. Qed.

Lemma wr_at_sub : forall (m : word -> option byte) a n a' n', wr_at psegs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> wr_at psegs m a' n'.
Proof.
  intros m a n a' n' (Ha & Hn & H) H1 H0 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma bytes_at_app : forall (m : word -> option byte) A bs1 bs2,
  bytes_at psegs m A (bs1 ++ bs2) -> bytes_at psegs m A bs1 /\ bytes_at psegs m (A + Z.of_nat (length bs1)) bs2.
Proof.
  intros m A bs1 bs2 (H0 & H1 & HB). rewrite length_app in H1. split.
  - split; [lia|]. split; [lia|]. intros i Hi. rewrite (HB i) by (rewrite length_app; lia). rewrite nth_error_app1 by lia. reflexivity.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (length bs1) + Z.of_nat i) with (A + Z.of_nat (length bs1 + i)) by lia.
    rewrite (HB (length bs1 + i)%nat) by (rewrite length_app; lia). rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma rw_cells_app_split : forall (m : word -> option byte) A cs1 cs2,
  rw_cells psegs m A (cs1 ++ cs2) -> rw_cells psegs m A cs1 /\ rw_cells psegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf HB] HW]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in HW. destruct HW as (X0 & X1 & HWi).
  split; (split; [split; assumption|]).
  - split; [lia|]. split; [lia|]. intros i Hi. apply HWi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply HWi. lia.
Qed.

Lemma file_cells_size : forall a b c d e f g h i j k, cells_size (file_cells a b c d e f g h i j k) = 232%nat.
Proof. intros. reflexivity. Qed.

Lemma mod32_of_wrap : forall e, bv_unsigned (Z_to_bv 64 e) mod 2^32 = e mod 2^32.
Proof.
  intros e. rewrite unsigned_lit_wrap. change (2^64) with (2^32 * 2^32). apply Zaux.Zmod_mod_mult; lia.
Qed.

Lemma zbytes_pbytes : forall payload, Forall (fun c => 0 <= c < 256) payload -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zbytes (map (Z_to_bv 8) payload) = payload.
Proof.
  intros payload HF. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zbytes. rewrite map_map. induction HF as [|c l Hc _ IH]; cbn [map]; [reflexivity|].
  f_equal; [| exact IH]. apply Z_to_bv_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma zeros_at_of_chunk : forall (m : word -> option byte) A k,
  rw_cells psegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))] -> 0 <= k -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m A k.
Proof.
  intros m A k [[Hwf HB] HW] Hk. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at. rewrite <- ?rdn_conv.
  pose proof (bytes_at_rdn psegs m A _ 0 (Z.to_nat k) HB ltac:(rewrite repeat_length; lia)) as X.
  cbn [skipn] in X. rewrite firstn_repeat in X by lia. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma zeros_at_sub : forall (m : word -> option byte) A k o j,
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m A k -> 0 <= o -> 0 <= j -> o + j <= k -> 0 <= A -> A + k <= 2^64 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (A + o) j.
Proof.
  intros m A k o j HZ Ho Hj Hk HA HAk. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at in *. rewrite <- ?rdn_conv in *.
  pose proof (bytes_at_of_rdn m _ A _ HZ HA ltac:(lia)) as BY.
  pose proof (bytes_at_rdn psegs m A _ (Z.to_nat o) (Z.to_nat j) BY ltac:(rewrite repeat_length; lia)) as X.
  rewrite skipn_repeat, firstn_repeat in X by lia. unfold wa in X. rewrite Z2Nat.id in X by lia. exact X.
Qed.

Lemma cell8_same_on : forall (P : Z -> Prop) m m' a v,
  same_on P m m' -> (forall x, a <= x < a + 8 -> P x) -> 0 <= a -> a + 8 <= 2^64 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m a v -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' a v.
Proof. intros P m m' a v SO HP Ha H8 H. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 in *. rewrite <- ?rdn_conv in *. rewrite (rdn_same_on P m m' a 8 SO); [exact H| exact HP| lia| cbn; lia]. Qed.

Lemma zeros_at_same_on : forall (P : Z -> Prop) m m' a k,
  same_on P m m' -> (forall x, a <= x < a + k -> P x) -> 0 <= a < 2^64 -> 0 <= k -> a + k <= 2^64 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m a k -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m' a k.
Proof.
  intros P m m' a k SO HP Ha Hk Hak H. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at in *. rewrite <- ?rdn_conv in *.
  rewrite (rdn_same_on P m m' a (Z.to_nat k) SO); [exact H| intros x Hx; apply HP; lia| lia| lia].
Qed.

Lemma holds_same_on : forall (P : Z -> Prop) m m' a zs,
  same_on P m m' -> (forall x, a <= x < a + Z.of_nat (length zs) -> P x) -> 0 <= a < 2^64 -> a + Z.of_nat (length zs) <= 2^64 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m a zs -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m' a zs.
Proof.
  intros P m m' a zs SO HP Ha Hak H. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds in *. rewrite <- ?rdn_conv in *.
  rewrite (rdn_same_on P m m' a (length zs) SO); [exact H| exact HP| lia| lia].
Qed.

Lemma rdn_of_bytes_at : forall (m : word -> option byte) D bs,
  bytes_at psegs m D bs -> OP.rdn psegs m (Z_to_bv 64 D) (length bs) = Some bs.
Proof.
  intros m D bs BY. rewrite rdn_conv. pose proof (bytes_at_rdn psegs m D bs 0 (length bs) BY ltac:(lia)) as X.
  cbn [skipn] in X. rewrite firstn_all in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma relro_of_hc : forall m, harness_cells m -> relro_pristine m.
Proof.
  intros m HC x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply HC. unfold RELRO_LO, RELRO_HI, PRELRO_LO, PRELRO_HI in *. exact Hx.
Qed.

Section CANSEC0. Context {rc : runConstT}.
Lemma RHEAP_ssp_fl : forall s LB m, RHEAP s LB m -> ssp_cells m CAN.
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
  unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.
End CANSEC0.

Section MRULES. Context {rc : runConstT}.
Lemma implM_getb : forall {A} (f : PState -> M PState A) (s : PState) Q ms,
  implM psegs (f s) s Q ms -> implM psegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. exact H. Qed.

Lemma implM_unrb : forall {A B} (f : A -> M PState B) (s : PState) Q ms, implM psegs (mbind munr f) s Q ms.
Proof. intros A B f s Q ms. unfold implM, mbind, munr, ebind. cbn [ITree.bind]. apply impl_ret_unr. Qed.

Lemma implM_creq : forall {B} (N : Z) (K : bptr -> M PState B) (s : PState) (P1 : option bptr -> PState -> machine_state -> Prop) Q ms,
  implM psegs (raw_malloc N) s P1 ms ->
  (forall p s' ms', P1 (Some p) s' ms' -> implM psegs (K p) s' Q ms') ->
  implM psegs (mbind (HarnessC.creq raw_malloc N) K) s Q ms.
Proof.
  intros B N K s P1 Q ms HM HK. unfold HarnessC.creq. apply implM_bind_assoc.
  eapply implM_bind; [exact HM|]. cbv beta. intros [p|] s' ms' PO; [| apply implM_unrb].
  apply implM_retb. exact (HK p s' ms' PO).
Qed.

Lemma implM_zreq : forall {B} (N : Z) (K : bptr -> M PState B) (s : PState) (P1 : option bptr -> PState -> machine_state -> Prop) Q ms,
  implM psegs (raw_malloc N) s P1 ms ->
  (forall p s' ms', P1 (Some p) s' ms' -> fresh_top s s' p -> implM psegs (K p) s' Q ms') ->
  implM psegs (mbind (HarnessC.zreq raw_malloc fresh_topb N) K) s Q ms.
Proof.
  intros B N K s P1 Q ms HM HK. unfold HarnessC.zreq. apply implM_bind_assoc. apply implM_getb. apply implM_bind_assoc.
  eapply implM_bind; [exact HM|]. cbv beta. intros [p|] s' ms' PO; [| apply implM_unrb].
  apply implM_bind_assoc. apply implM_getb. destruct (fresh_topb s s' p) eqn:FR; [| apply implM_unrb].
  apply implM_retb. apply (HK p s' ms' PO). apply fresh_topb_true. exact FR.
Qed.
End MRULES.

Definition A_FMT_zerr_fl : Z := 0x102f2.
Definition PFPRINTF_fl : Z := 0x25774.
Definition ZERR_MSGS : list (Z * list Z) :=
  [(0x1030b, HarnessC.MSG_DEFLATEEND); (0x10570, HarnessC.MSG_INFLATE); (0x103f9, HarnessC.MSG_INFLATESYNC)].
Section CANSEC_FPR. Context {rc : runConstT}.
Section ZErrFl.
  Context {St : Type}.
  Definition fprintf_zerr_post_fl (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.
  Definition fprintf_zerr_stmt_fl (amsg : Z) (msg : list Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (e : Z) (lo : Z) (canary : word),
      fwritex_stderr_stmt -> stdio_write_flush_stmt ->
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_zerr_fl -> a2 = Z_to_bv 64 amsg ->
      (-2^31 <= e < 2^31) -> bv_unsigned a3 mod 2^32 = e mod 2^32 ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^47) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      implM psegs (stderr_fprintf (HarnessC.pieces_zerr msg e) : M St unit) st
            (fprintf_zerr_post_fl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 PFPRINTF_fl) fc None m (seg_rom psegs)).
End ZErrFl.
End CANSEC_FPR.

Section CANSEC1. Context {rc : runConstT}.
Section CALL.
Variable FLM : flush_model.
Variable FLIB : forall fx : OP.FPState, @fl_lib fx.
Hypothesis MALLOCZ : rmalloc_stmt_z.
Hypothesis CALLOC : rcalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FPRINTF : forall amsg msg, In (amsg, msg) ZERR_MSGS -> @fprintf_zerr_stmt_fl PState amsg msg.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.

Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem)
          (st0 : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z).
Notation usp := (bv_unsigned sp).
Notation n := (zlength payload).
Notation cl0 := (CLEN (zlength payload)).
Notation CT := (FLIB (OP.mkFP F fc)).
Hypothesis FP : Forall (fun c => 0 <= c < 256) payload.
Hypothesis D16 : D mod 16 = 0.
Hypothesis D0 : 0 < D.
Hypothesis DT : D + n <= ATOP.
Hypothesis PL : n < 2^26.
Hypothesis SPAB : usp <= AB.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= usp - HARNESS_STACK.
Hypothesis FRM : frm0 fc.
Hypothesis TP : tp = wz RATP.
Hypothesis SP16 : usp mod 16 = 0.
Hypothesis RAE : bv_unsigned ra mod 2 = 0.
Hypothesis SP47 : usp <= 2^47.
Hypothesis PB : (n = 0 /\ D = PEMPTY) \/ exists b, In b LB /\ blk_addr b <= D /\ D + n <= blk_addr b + blk_size b.
Variable WB : ZPG.blk.

Notation POST := (fuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st0 LB AB lo m0).
Notation pbytes := (map (Z_to_bv 8) payload).
Notation HF pad clx := (LFC pad clx s2 s1 s0 ra).

Lemma n_nonneg : 0 <= n. Proof. unfold zlength. lia. Qed.
Lemma usp_facts : 0x7fff7f800000 <= usp < 2^64 /\ 0x7fff7f800000 <= ATOP /\ ATOP + 16384 <= usp /\ (usp - 208) mod 16 = 0.
Proof.
  pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  pose proof atop_range as AR. unfold HARNESS_STACK in LO.
  split; [lia|]. split; [lia|]. split; [lia|].
  replace (usp - 208) with (usp + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact SP16.
Qed.
Lemma cl_eq : fl_cl n = cl0. Proof. reflexivity. Qed.

Record MID (LBx : list block) (clx : Z) (s : PState) (m : mem) : Prop := {
  md_heap : RHEAP s (LBx ++ LB) m;
  md_mi   : mem_inv psegs m;
  md_stk  : stk psegs m lo usp;
  md_err  : exists errv : word, rw_cells psegs m (errno_addr tp) [C4 errv];
  md_aux  : rauxv_ok m AB;
  md_pres : harness_pres LB usp m0 m;
  md_so   : ps_so s = ps_so st0;
  md_hc   : harness_cells m;
  md_sf   : stderr_wfile0 m;
  md_hf   : exists pad, rw_cells psegs m (usp - 48) (HF pad clx);
  md_clx  : 0 <= clx < 2^63;
  md_st   : rw_cells psegs m HDATA [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 D)];
  md_pay  : bytes_at psegs m D pbytes;
  md_pwr  : wr_at psegs m D n;
  md_wr   : Forall (fun b => wr_at psegs m (blk_addr b) (blk_size b)) LBx }.

Lemma MID_blk : forall LBx clx s m b, MID LBx clx s m -> In b (LBx ++ LB) -> rblock_range (blk_addr b) (blk_size b).
Proof. intros LBx clx s m b H Hb. exact (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b (md_heap _ _ _ _ H) Hb). Qed.

Lemma MID_disj : forall LBx clx s m b1 b2, MID LBx clx s m -> In b1 LBx -> In b2 LB ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros LBx clx s m b1 b2 H H1 H2.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  apply (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b1 b2 (md_heap _ _ _ _ H)); [apply in_or_app; left; exact H1| apply in_or_app; right; exact H2|].
  rewrite map_app in ND. intros E. apply (nodup_app_disj _ _ (blk_id b1) ND); [apply in_map; exact H1| rewrite E; apply in_map; exact H2].
Qed.

Lemma MID_apart : forall LBx clx s m (i j : nat) b1 b2, MID LBx clx s m ->
  nth_error LBx i = Some b1 -> nth_error LBx j = Some b2 -> i <> j ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart (blk_addr b1) (blk_size b1) (blk_addr b2) (blk_size b2).
Proof.
  intros LBx clx s m i j b1 b2 H N1 N2 NE. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND. rewrite map_app in ND. apply NoDup_app_l in ND.
  apply (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b1 b2 (md_heap _ _ _ _ H));
    [apply in_or_app; left; eapply nth_error_In; exact N1| apply in_or_app; left; eapply nth_error_In; exact N2|].
  intros E. apply NE. apply (proj1 (NoDup_nth_error _) ND i j).
  - rewrite length_map. apply (proj1 (nth_error_Some LBx i)). rewrite N1. discriminate.
  - rewrite !nth_error_map, N1, N2. cbn. f_equal. exact E.
Qed.

Lemma MID_pay_apart : forall LBx clx s m b, MID LBx clx s m -> 1 <= n -> In b LBx -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart D n (blk_addr b) (blk_size b).
Proof.
  intros LBx clx s m b H N1 Hb. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart. destruct PB as [[E _]|(b2 & Hb2 & B1 & B2)]; [lia|].
  pose proof (MID_disj _ _ _ _ b b2 H Hb Hb2). lia.
Qed.

Lemma pay_img : 1 <= n -> forall LBx clx s m, MID LBx clx s m -> D + n <= 0x10000 \/ 0x5f000 <= D.
Proof.
  intros N1 LBx clx s m H. destruct PB as [[E _]|(b2 & Hb2 & B1 & B2)]; [lia|].
  pose proof (MID_blk _ _ _ _ b2 H ltac:(apply in_or_app; right; exact Hb2)) as (_ & _ & _ & _ & Q5). lia.
Qed.

Lemma MID_perm : forall LBx LBx' clx s m, MID LBx clx s m -> Permutation.Permutation LBx LBx' -> MID LBx' clx s m.
Proof.
  intros LBx LBx' clx s m H P. destruct H. constructor; try assumption.
  - eapply RHEAP_perm; [eassumption|]. apply Permutation.Permutation_app_tail. exact P.
  - eapply Permutation.Permutation_Forall; [exact P| assumption].
Qed.

Lemma blk_okz_of_MID : forall LBx clx s m (pp : bptr) A k,
  MID LBx clx s m -> In (pp, A, k) LBx -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.blk_okz psegs m FL_IMG_TOP ATOP A k.
Proof.
  intros LBx clx s m pp A k H Hin.
  pose proof (MID_blk _ _ _ _ (pp, A, k) H ltac:(apply in_or_app; left; exact Hin)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5.
  pose proof (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) _ Hin) as WR. cbn [blk_addr blk_size fst snd] in WR.
  unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.blk_okz, FL_IMG_TOP. repeat split; try lia.
  pose proof (wr_at_store_ok psegs m A k 0 (Z.to_nat k) WR ltac:(lia) ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma apart_from_all_intro : forall a na (L : list block),
  (forall b, In b L -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart a na (blk_addr b) (blk_size b)) ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all a na (map (fun b => (blk_addr b, blk_size b)) L).
Proof.
  intros a na L HL. induction L as [|b L IH]; cbn; [exact I|]. split; [apply HL; left; reflexivity| apply IH; intros b' Hb'; apply HL; right; exact Hb'].
Qed.

Lemma all_apart_of_blocks : forall (L : list block),
  List.NoDup (map blk_id L) ->
  (forall b1 b2, In b1 L -> In b2 L -> blk_id b1 <> blk_id b2 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart (blk_addr b1) (blk_size b1) (blk_addr b2) (blk_size b2)) ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart (map (fun b => (blk_addr b, blk_size b)) L).
Proof.
  induction L as [|b L IH]; intros ND HP; cbn; [exact I|]. cbn in ND. inversion ND as [|? ? NI ND']; subst. split.
  - apply apart_from_all_intro. intros b2 Hb2. apply HP; [left; reflexivity| right; exact Hb2|].
    intros E. apply NI. rewrite E. apply in_map. exact Hb2.
  - apply IH; [exact ND'|]. intros b1 b2 H1 H2 NE. apply HP; [right; exact H1| right; exact H2| exact NE].
Qed.

Lemma MID_all_apart : forall LBx clx s m, MID LBx clx s m -> 1 <= n ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart ((D, n) :: map (fun b => (blk_addr b, blk_size b)) (rev LBx)).
Proof.
  intros LBx clx s m H N1. cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart]. split.
  - apply apart_from_all_intro. intros b Hb. apply (MID_pay_apart LBx clx s m b H N1). apply in_rev. exact Hb.
  - pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND. rewrite map_app in ND. apply NoDup_app_l in ND.
    apply all_apart_of_blocks.
    + rewrite map_rev. apply NoDup_rev. exact ND.
    + intros b1 b2 H1 H2 NE. apply in_rev in H1. apply in_rev in H2.
      apply (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b1 b2 (md_heap _ _ _ _ H)); [apply in_or_app; left; exact H1| apply in_or_app; left; exact H2| exact NE].
Qed.

Lemma pay_same_on : forall (P : Z -> Prop) m m',
  same_on P m m' -> (forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> P a) ->
  bytes_at psegs m D pbytes -> bytes_at psegs m' D pbytes.
Proof.
  intros P m m' SO HP BY. eapply bytes_at_magree; [exact SO| exact BY|].
  intros a Ha. rewrite length_map in Ha. destruct PB as [[E _]|(b & Hb & B1 & B2)].
  - exfalso. unfold zlength in E. lia.
  - apply (HP b a Hb). unfold zlength in B2. lia.
Qed.
Lemma pwr_same_on : forall (P : Z -> Prop) m m',
  same_on P m m' -> (forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> P a) ->
  wr_at psegs m D n -> wr_at psegs m' D n.
Proof.
  intros P m m' SO HP WR. eapply wr_at_magree; [exact SO| exact WR|].
  intros a Ha. destruct PB as [[E _]|(b & Hb & B1 & B2)]; [exfalso; lia|]. apply (HP b a Hb). lia.
Qed.

Lemma statics_client : forall LBp SPc a,
  (HDATA <= a < HDATA + 16 \/ RSTDERR <= a < RSTDERR + 232 \/ PRELRO_LO <= a < PRELRO_HI \/ RERRNO <= a < RERRNO + 4) ->
  ATOP <= SPc -> rclient_addr LBp SPc a \/ (RERRNO <= a < RERRNO + 4).
Proof.
  intros LBp SPc a Ha HS. unfold HDATA, PRELRO_LO, PRELRO_HI, RERRNO in *.
  destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [left| left| left| right; exact Ha]; right; left;
    unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia.
Qed.

Lemma MID_heap : forall LBx LBx' LBp clx s s' m m' SPc,
  MID LBx clx s m ->
  rheap_pres LBp SPc m m' -> (forall b, In b LB -> In b LBp) ->
  (forall b, In b LBx' -> (In b LBx /\ In b LBp) \/ wr_at psegs m' (blk_addr b) (blk_size b)) ->
  lo <= SPc <= usp - 48 ->
  RHEAP s' (LBx' ++ LB) m' -> mem_inv psegs m' -> stk psegs m' lo SPc ->
  (exists errv : word, rw_cells psegs m' (errno_addr tp) [C4 errv]) -> rauxv_ok m' AB -> ps_so s' = ps_so s ->
  MID LBx' clx s' m'.
Proof.
  intros LBx LBx' LBp clx s s' m m' SPc H HP SUBL SUB HS HH' MI' ST' ER' AX' SO'.
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  pose proof (same_on_rheap_pres _ _ _ _ HP) as SO.
  assert (STC : forall a, (HDATA <= a < HDATA + 16 \/ RSTDERR <= a < RSTDERR + 232 \/ PRELRO_LO <= a < PRELRO_HI) -> rclient_addr LBp SPc a).
  { intros a Ha. destruct (statics_client LBp SPc a ltac:(tauto) ltac:(lia)) as [X|X]; [exact X|].
    exfalso. unfold HDATA, PRELRO_LO, PRELRO_HI, RERRNO in *. lia. }
  constructor.
  - exact HH'.
  - exact MI'.
  - destruct (stk_split psegs m lo SPc usp (md_stk _ _ _ _ H) ltac:(lia)) as [_ STu].
    eapply stk_merge; [exact ST'| eapply rheap_pres_stk; [exact HP| exact STu| lia]| lia].
  - exact ER'.
  - exact AX'.
  - eapply harness_pres_trans; [exact (md_pres _ _ _ _ H)|]. apply harness_pres_of_heap.
    eapply rheap_pres_weaken; [exact HP| lia| exact SUBL].
  - rewrite SO'. exact (md_so _ _ _ _ H).
  - intros a Ha. destruct (SO a ltac:(unfold PRELRO_LO, PRELRO_HI in Ha; lia) ltac:(apply STC; tauto)) as [E _].
    unfold wa in E. rewrite E. exact (md_hc _ _ _ _ H a Ha).
  - destruct (md_sf _ _ _ _ H) as (flags & mode & e & wend & tail & FC & FL & WE & HE). exists flags, mode, e, wend, tail.
    split; [| split; [exact FL| split; [exact WE| exact HE]]].
    eapply rw_cells_magree; [exact SO| exact FC|]. intros a Ha. rewrite file_cells_size in Ha. apply STC. right; left. exact Ha.
  - destruct (md_hf _ _ _ _ H) as [pad HFc]. exists pad. eapply rw_cells_magree; [exact SO| exact HFc|]. intros a Ha. left. cbn in Ha. lia.
  - exact (md_clx _ _ _ _ H).
  - eapply rw_cells_magree; [exact SO| exact (md_st _ _ _ _ H)|]. intros a Ha. apply STC. left. cbn in Ha. unfold HDATA in *. lia.
  - eapply pay_same_on; [exact SO| | exact (md_pay _ _ _ _ H)].
    intros b a Hb Ha. right; right. exists b. split; [apply SUBL; exact Hb| exact Ha].
  - eapply pwr_same_on; [exact SO| | exact (md_pwr _ _ _ _ H)].
    intros b a Hb Ha. right; right. exists b. split; [apply SUBL; exact Hb| exact Ha].
  - apply Forall_forall. intros b Hb. destruct (SUB b Hb) as [[Hb' Hp]|WR]; [| exact WR].
    eapply rheap_pres_wr_at; [exact HP| exact (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) b Hb')|].
    right; right. exists b. split; [exact Hp| lia].
Qed.

Definition fp_ok (LBx : list block) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= usp - 48)
  \/ (exists b, In b LBx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Definition fp_okF (LBx : list block) (iv : Z * Z) : Prop := fp_ok LBx iv \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232).

Lemma MID_munch_gen : forall LBx clx s m m' W,
  MID LBx clx s m -> munch W m m' -> wmono psegs m m' -> mem_inv psegs m' -> Forall (fp_okF LBx) W -> stderr_wfile0 m' -> MID LBx clx s m'.
Proof.
  intros LBx clx s m m' W H MU WM MI' FW SF'.
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  assert (BLK : forall b, In b (LBx ++ LB) -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (MID_blk _ _ _ _ b H Hb)).
  assert (OUT : forall x, (usp - 48 <= x \/ (0x10000 <= x < 0x5f000 /\ ~ (RSTDERR <= x < RSTDERR + 232))
                           \/ (exists b, In b LB /\ blk_addr b <= x < blk_addr b + blk_size b)) -> outside W x).
  { intros x Hx. apply (outside_Forall _ _ x FW). intros [a b] [[K|(blk & Hb & K1 & K2)]|[K1 K2]]; cbn [fst snd] in *; intros IN.
    - destruct Hx as [Hx|[[Hx _]|(b2 & Hb2 & Hx)]]; try lia.
      pose proof (BLK b2 ltac:(apply in_or_app; right; exact Hb2)) as (_ & _ & _ & B4 & _). lia.
    - pose proof (BLK blk ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & B4 & B5).
      destruct Hx as [Hx|[[Hx _]|(b2 & Hb2 & Hx)]]; try lia.
      pose proof (MID_disj _ _ _ _ blk b2 H Hb Hb2). lia.
    - subst. destruct Hx as [Hx|[[Hx NF]|(b2 & Hb2 & Hx)]]; try lia.
      pose proof (BLK b2 ltac:(apply in_or_app; right; exact Hb2)) as (_ & _ & _ & _ & B5). lia. }
  constructor.
  - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact (md_heap _ _ _ _ H)| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [a b] [[K|(blk & Hb & K1 & K2)]|[K1 K2]]; cbn [fst snd] in *.
    + left. cbn [fst]. lia.
    + right; right. exists blk. split; [apply in_or_app; left; exact Hb| cbn [fst snd]; lia].
    + subst. right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
  - exact MI'.
  - eapply stk_wmono; [exact (md_stk _ _ _ _ H)| lia| exact WM].
  - destruct (md_err _ _ _ _ H) as [errv ER]. exists errv. eapply rw_cells_magree; [exact SO| exact ER|].
    intros a Ha. apply OUT. right; left. rewrite TP in Ha. unfold wz, RATP in Ha. rewrite unsigned_lit in Ha by lia.
    change (Z.of_nat (cells_size [C4 errv])) with 4 in Ha. lia.
  - eapply rauxv_ok_frame; [exact (md_aux _ _ _ _ H)| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [a b] [[K|(blk & Hb & K1 & K2)]|[K1 K2]]; cbn [fst snd] in *; unfold RAUXV_CELL.
    + split; [lia| right; lia].
    + pose proof (BLK blk ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & B4 & B5). split; [lia| lia].
    + subst. split; [lia| left; lia].
  - eapply harness_pres_trans; [exact (md_pres _ _ _ _ H)|]. intros a Ha Hc NB. apply SO; [exact Ha|]. apply OUT.
    destruct Hc as [Hc|[[Hc NS]|(b & Hb & Hr)]]; [left; lia| right; left; split; [lia| unfold hown_addr in NB; tauto]|].
    right; right. exists b. split; [exact Hb| exact Hr].
  - exact (md_so _ _ _ _ H).
  - intros a Ha. destruct (SO a ltac:(unfold PRELRO_LO, PRELRO_HI in Ha; lia) ltac:(apply OUT; right; left; unfold PRELRO_LO, PRELRO_HI in *; lia)) as [E _].
    unfold wa in E. rewrite E. exact (md_hc _ _ _ _ H a Ha).
  - exact SF'.
  - destruct (md_hf _ _ _ _ H) as [pad HFc]. exists pad. eapply rw_cells_magree; [exact SO| exact HFc|]. intros a Ha. apply OUT. left. cbn in Ha. lia.
  - exact (md_clx _ _ _ _ H).
  - eapply rw_cells_magree; [exact SO| exact (md_st _ _ _ _ H)|]. intros a Ha. apply OUT. right; left. cbn in Ha. unfold HDATA in *. lia.
  - eapply pay_same_on; [exact SO| | exact (md_pay _ _ _ _ H)].
    intros b a Hb Ha. apply OUT. right; right. exists b. split; [exact Hb| exact Ha].
  - eapply pwr_same_on; [exact SO| | exact (md_pwr _ _ _ _ H)].
    intros b a Hb Ha. apply OUT. right; right. exists b. split; [exact Hb| exact Ha].
  - eapply Forall_impl; [| exact (md_wr _ _ _ _ H)]. intros b (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|].
    intros i Hi. apply WM. apply W2. exact Hi.
Qed.

Lemma MID_munch : forall LBx clx s m m' W,
  MID LBx clx s m -> munch W m m' -> wmono psegs m m' -> mem_inv psegs m' -> Forall (fp_ok LBx) W -> MID LBx clx s m'.
Proof.
  intros LBx clx s m m' W H MU WM MI' FW. pose proof usp_facts as (U1 & U2 & U3 & U4).
  apply (MID_munch_gen LBx clx s m m' W H MU WM MI'); [eapply Forall_impl; [| exact FW]; intros iv Hiv; left; exact Hiv|].
  destruct (md_sf _ _ _ _ H) as (flags & mode & e & wend & tail & FC & FL & WE & HE). exists flags, mode, e, wend, tail.
  split; [| split; [exact FL| split; [exact WE| exact HE]]].
  eapply rw_cells_magree; [exact (same_on_munch _ _ _ MU WM)| exact FC|]. intros a Ha. rewrite file_cells_size in Ha.
  apply (outside_Forall _ _ a FW). intros [x y] [K|(blk & Hb & K1 & K2)]; cbn [fst snd] in *; [lia|].
  pose proof (MID_blk _ _ _ _ blk H ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & B4 & B5). lia.
Qed.

Lemma MID_stdio : forall LBx clx s m m' SPc,
  MID LBx clx s m -> munch [(lo, SPc); (RSTDERR, RSTDERR + 232)] m m' -> wmono psegs m m' -> mem_inv psegs m' -> stderr_wfile0 m' ->
  SPc <= usp - 48 -> MID LBx clx s m'.
Proof.
  intros LBx clx s m m' SPc H MU WM MI' SF' HS. apply (MID_munch_gen LBx clx s m m' _ H MU WM MI'); [| exact SF'].
  apply Forall_cons; [left; left; cbn [fst snd]; lia|]. apply Forall_cons; [right; cbn [fst snd]; split; reflexivity| apply Forall_nil].
Qed.

Lemma MID_fm : forall LBx clx s m m' rs,
  MID LBx clx s m -> OF.frame_mod m m' rs -> Forall (fp_ok LBx) (fm_ivs rs) -> MID LBx clx s m'.
Proof.
  intros LBx clx s m m' rs H FM FW. destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
  apply (MID_munch LBx clx s m m' _ H MU WM); [| exact FW].
  eapply mem_inv_munch; [exact (md_mi _ _ _ _ H)| exact MU|].
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  intros a Ha. apply (outside_Forall _ _ a FW). intros [x y] [K|(blk & Hb & K1 & K2)]; cbn [fst snd] in *; [lia|].
  pose proof (MID_blk _ _ _ _ blk H ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & B4 & B5). lia.
Qed.

Lemma MID_stk_below : forall LBx clx s m SPc, MID LBx clx s m -> lo <= SPc <= usp -> stk psegs m lo SPc.
Proof. intros LBx clx s m SPc H HS. exact (proj1 (stk_split psegs m lo SPc usp (md_stk _ _ _ _ H) HS)). Qed.
Lemma MID_ssp : forall LBx clx s m, MID LBx clx s m -> ssp_cells m CAN.
Proof. intros LBx clx s m H. exact (RHEAP_ssp_fl _ _ _ (md_heap _ _ _ _ H)). Qed.

Lemma MID_ro : forall LBx clx s m, MID LBx clx s m -> forall i, FL_RO_LO <= i < FL_RO_HI -> m (Z_to_bv 64 i) = None.
Proof.
  intros LBx clx s m H i Hi. unfold FL_RO_LO, FL_RO_HI in Hi.
  destruct (Z.lt_ge_cases i 0x2c000); [apply (pristine_of_mem_inv m (md_mi _ _ _ _ H)); lia|].
  apply (md_hc _ _ _ _ H). unfold PRELRO_LO, PRELRO_HI. lia.
Qed.


Section RUN.
Hypothesis NR : 4 <= n <= 2^20.
Hypothesis LNK : forall fx, fl_links (FLIB fx) FLM WB payload.
Notation cmp := (fm_compr FLM payload).
Notation clen := (fm_clen FLM payload).
Notation cDSV1 := (DSV1 CT payload).      Notation cDX1 := (DX1 CT payload).        Notation cDRC1 := (DRC1 CT payload).
Notation cDOUT1 := (DOUT1 CT payload).    Notation cDNOUT1 := (DNOUT1 CT payload).  Notation cDNIN1 := (DNIN1 CT payload).
Notation cDZR1 := (DZR1 CT payload).      Notation cLC1 := (LC1 CT payload).        Notation cB3 := (B3 CT payload).
Notation cLC1' := (LC1' CT payload).      Notation cDZC2 := (DZC2 CT payload).      Notation cDSV2 := (DSV2 CT payload).
Notation cDX2 := (DX2 CT payload).        Notation cDRC2 := (DRC2 CT payload).      Notation cDOUT2 := (DOUT2 CT payload).
Notation cDNOUT2 := (DNOUT2 CT payload).  Notation cDZR2 := (DZR2 CT payload).      Notation cLC2 := (LC2 CT payload).
Notation cDTOT := (DTOT CT payload).
Definition REST (pc pu : bptr) : M PState Z := raw_free pc ;;; raw_free pu ;;; mret 0.

Lemma cl_range : 126 <= cl0 < 2^22.
Proof. pose proof n_nonneg. split; [apply CLEN_ge; lia| apply CLEN_lt32; lia]. Qed.

Lemma L_ret : forall LK clx s m (F1 : bvmap 5 word) (fc1 : bv 32) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID LK clx s m -> leak_ok LK -> frm0 fc1 ->
  implM psegs (mret 0) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x16380) fc1 None m (seg_rom psegs)).
Proof.
  intros LK clx s m F1 fc1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 H LOK FRM1.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  destruct (md_hf _ _ _ _ H) as [pad HFc]. destruct (md_err _ _ _ _ H) as [errv ER]. pose proof (md_clx _ _ _ _ H) as CLX.
  apply implM_ret.
  eapply (fl_seg_ret usp); [| apply (MID_stk_below _ _ _ _ _ H); lia| exact HFc|]; [lia|].
  intros STK. unfold fuzz_one_post.
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F1, fc1, m, errv, LK.
  rewrite (Z_to_bv_bv_unsigned sp).
  split; [reflexivity|]. split; [lia|]. split; [exact (md_mi _ _ _ _ H)|]. split; [exact FRM1|]. split; [exact STK|].
  split; [exact ER|]. split; [exact (md_aux _ _ _ _ H)|]. split; [exact (md_pres _ _ _ _ H)|]. split; [exact (md_heap _ _ _ _ H)|].
  split; [exact LOK|]. split; [exact (md_hc _ _ _ _ H)|]. split; [exact (md_sf _ _ _ _ H)|]. exact (md_so _ _ _ _ H).
Qed.

Lemma L_fin2 : forall LK clx s m (F1 : bvmap 5 word) (fc1 : bv 32) (pu : bptr) (up : Z)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID ((pu, up, n) :: LK) clx s m -> leak_ok LK -> frm0 fc1 ->
  implM psegs (raw_free pu ;;; mret 0) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -48)) gp tp x5 x6 x7 x8 (Z_to_bv 64 up) x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x16378) fc1 None m (seg_rom psegs)).
Proof.
  intros LK clx s m F1 fc1 pu up x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 H LOK FRM1.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  destruct (md_err _ _ _ _ H) as [errv ER].
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply fl_seg_fin2; reflexivity| intros ms' ->].
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (pu, up, n) :: (LK ++ LB)) (p := pu) (A := up) (n := n) (errv := errv);
      rewrite ?(unsigned_lit (usp + -48)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -48)) in ST' by lia. rewrite ?(unsigned_lit (usp + -48)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove pu ((pu, up, n) :: (LK ++ LB))) with (LK ++ LB) in HPR, HEAP' by (symmetry; apply (RDriver_facts.lb_remove_head (pu, up, n)); exact ND).
  assert (H' : MID LK clx s' m').
  { apply (MID_heap ((pu, up, n) :: LK) LK (LK ++ LB) clx s s' m m' (usp + -48) H);
      [exact HPR| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_ret LK clx s' m' F1 fc1); [exact H'| exact LOK| exact FRM1].
Qed.

Lemma L_fin1 : forall LK clx s m (F1 : bvmap 5 word) (fc1 : bv 32) (pc pu : bptr) (cp up : Z)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID ((pc, cp, cl0) :: (pu, up, n) :: LK) clx s m -> leak_ok LK -> frm0 fc1 ->
  implM psegs (REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -48)) gp tp x5 x6 x7 x8 (Z_to_bv 64 up) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 cp) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x16370) fc1 None m (seg_rom psegs)).
Proof.
  intros LK clx s m F1 fc1 pc pu cp up x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H LOK FRM1.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  destruct (md_err _ _ _ _ H) as [errv ER].
  unfold REST.
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply fl_seg_fin1; reflexivity| intros ms' ->].
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (pc, cp, cl0) :: ((pu, up, n) :: LK ++ LB)) (p := pc) (A := cp) (n := cl0) (errv := errv);
      rewrite ?(unsigned_lit (usp + -48)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -48)) in ST' by lia. rewrite ?(unsigned_lit (usp + -48)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove pc ((pc, cp, cl0) :: ((pu, up, n) :: LK ++ LB))) with ((pu, up, n) :: LK ++ LB) in HPR, HEAP' by (symmetry; apply (RDriver_facts.lb_remove_head (pc, cp, cl0)); exact ND).
  assert (H' : MID ((pu, up, n) :: LK) clx s' m').
  { apply (MID_heap ((pc, cp, cl0) :: (pu, up, n) :: LK) ((pu, up, n) :: LK) ((pu, up, n) :: LK ++ LB) clx s s' m m' (usp + -48) H);
      [exact HPR| intros b Hb; right; apply in_or_app; right; exact Hb
      | intros b Hb; left; split; [right; exact Hb| destruct Hb as [<-|Hb]; [left; reflexivity| right; apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_fin2 LK clx s' m' F1 fc1 pu up); [exact H'| exact LOK| exact FRM1].
Qed.

Lemma L_ts_ret : forall (pc0 : Z), pc0 = 0x16298 \/ pc0 = 0x162d4 ->
  forall LK clx s m (F1 : bvmap 5 word) (fc1 : bv 32) (pc pu : bptr) (cp up : Z)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID ((pc, cp, cl0) :: (pu, up, n) :: LK) clx s m -> leak_ok LK -> frm0 fc1 ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  implM psegs (REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 pc0) fc1 None m (seg_rom psegs)).
Proof.
  intros pc0 HPC LK clx s m F1 fc1 pc pu cp up x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 H LOK FRM1 TS.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR.
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5, Q1, Q2, Q3, Q4, Q5.
  eapply implM_evt with (P := fun ms' => ms' = _);
    [eapply (fl_seg_ts_ret usp pc0 HPC _ n cp up); [exact NR| lia| lia| exact TS| exact (md_mi _ _ _ _ H)| reflexivity]| intros ms' ->].
  eapply (L_fin1 LK clx s m F1 fc1 pc pu cp up); [exact H| exact LOK| exact FRM1].
Qed.

Section INFL.
Variables (F1 : bvmap 5 word) (fc1 : bv 32).
Hypothesis FRM1 : frm0 fc1.
Notation CT1 := (FLIB (OP.mkFP F1 fc1)).
Let LNK1 : fl_links CT1 FLM WB payload := LNK (OP.mkFP F1 fc1).
Notation cIZC1 := (IZC1 FLM payload).     Notation cICALL1 := (ICALL1 CT1 FLM WB payload).
Notation cIS1 := (IS1 CT1 FLM WB payload). Notation cIR1 := (IR1 CT1 FLM WB payload).
Notation cICONS1 := (ICONS1 CT1 FLM WB payload).  Notation cINOUT1 := (INOUT1 CT1 FLM WB payload).
Notation cIZC2 := (IZC2 CT1 FLM WB payload).      Notation cIS2 := (IS2 CT1 FLM WB payload).   Notation cIR2 := (IR2 CT1 FLM WB payload).
Notation cICONS2 := (ICONS2 CT1 FLM WB payload).  Notation cIZC3 := (IZC3 CT1 FLM WB payload).
Notation cICALL3 := (ICALL3 CT1 FLM WB payload).  Notation cIS3 := (IS3 CT1 FLM WB payload).   Notation cIR3 := (IR3 CT1 FLM WB payload).
Lemma L_idiag : forall LK clx s m (pc pu : bptr) (cp up e amsg : Z) (msg : list Z)
    (x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID ((pc, cp, cl0) :: (pu, up, n) :: LK) clx s m -> leak_ok LK -> -2^31 <= e < 2^31 -> In (amsg, msg) ZERR_MSGS ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  implM psegs (HarnessC.diag_zerr msg e ;;; REST pc pu) s POST
    (MS (mkR (Z_to_bv 64 0x16298) (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 RSTDERR) (Z_to_bv 64 A_FMT_zerr_fl)
             (Z_to_bv 64 amsg) (Z_to_bv 64 e) x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 PFPRINTF_fl) fc1 None m (seg_rom psegs)).
Proof.
  intros LK clx s m pc pu cp up e amsg msg x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x28 x29 x30 x31 H LOK HE HIN TS.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  unfold HarnessC.diag_zerr.
  eapply implM_bind.
  { pose proof (FPRINTF amsg msg HIN) as FPR. unfold fprintf_zerr_stmt_fl in FPR.
    eapply (FPR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m s e lo CAN FWX SWF);
      rewrite ?(unsigned_lit (usp + -192)) by lia.
    - apply stderr_wfile0_wfile. exact (md_sf _ _ _ _ H).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact HE.
    - apply mod32_of_wrap.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - unfold FPRINTF_DEPTH. lia.
    - unfold GLOBALS_TOP. lia.
    - lia.
    - exact (MID_ssp _ _ _ _ H).
    - exact (md_mi _ _ _ _ H).
    - exact FRM1. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & Ft & fc1' & m' & -> & MU & WM & MI' & FRM1' & FK & ST' & SF' & SSP' & ->).
  rewrite ?(unsigned_lit (usp + -192)) in MU by lia.
  pose proof (MID_stdio _ _ s m m' (usp + -192) H MU WM MI' SF' ltac:(lia)) as H'.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  apply (L_ts_ret 0x16298 ltac:(left; reflexivity) LK clx s m' Ft fc1' pc pu cp up); [exact H'| exact LOK| exact FRM1'|].
  eapply rw_cells_magree; [exact (same_on_munch _ _ _ MU WM)| exact TS|]. intros a Ha. cbn in Ha. cbn. lia.
Qed.

Lemma L_ifw : forall LK clx s m (pc pu : bptr) (cp up : Z)
    (x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID ((pc, cp, cl0) :: (pu, up, n) :: LK) clx s m -> leak_ok LK ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  implM psegs (stderr_fwrite HarnessC.MSG_SHOULD ;;; REST pc pu) s POST
    (MS (mkR (Z_to_bv 64 0x162d4) (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0x1061a) (Z_to_bv 64 49) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR)
             x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x25910) fc1 None m (seg_rom psegs)).
Proof.
  intros LK clx s m pc pu cp up x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x28 x29 x30 x31 H LOK TS.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  eapply implM_bind.
  { unfold fwrite_diag_stmt in FWR.
    eapply (FWR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m s lo CAN HarnessC.MSG_SHOULD TOW);
      rewrite ?(unsigned_lit (usp + -192)), ?(unsigned_lit 0x1061a) by lia.
    - exact (md_sf _ _ _ _ H).
    - apply (bytes_at_pristine m 0x1061a 49); [| vm_compute; reflexivity| lia| cbn; lia].
      intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply (pristine_of_mem_inv m (md_mi _ _ _ _ H)). cbn in Hx. lia.
    - unfold HarnessC.MSG_SHOULD. cbn. repeat (constructor; [lia|]). constructor.
    - change (zlength HarnessC.MSG_SHOULD) with 49. lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - unfold FWRITE_DEPTH. lia.
    - unfold GLOBALS_TOP. lia.
    - lia.
    - change (zlength HarnessC.MSG_SHOULD) with 49. lia.
    - left. change (zlength HarnessC.MSG_SHOULD) with 49. lia.
    - left. change (zlength HarnessC.MSG_SHOULD) with 49. lia.
    - exact (MID_ssp _ _ _ _ H).
    - exact (md_mi _ _ _ _ H). }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MU & WM & MI' & ST' & SF' & SSP' & ->).
  rewrite ?(unsigned_lit (usp + -192)) in MU by lia.
  pose proof (MID_stdio _ _ s m m' (usp + -192) H MU WM MI' SF' ltac:(lia)) as H'.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  apply (L_ts_ret 0x162d4 ltac:(right; reflexivity) LK clx s m' F1 fc1 pc pu cp up); [exact H'| exact LOK| exact FRM1|].
  eapply rw_cells_magree; [exact (same_on_munch _ _ _ MU WM)| exact TS|]. intros a Ha. cbn in Ha. cbn. lia.
Qed.

Definition IE_CELLS (m : mem) (p w md : Z) : Prop :=
  OP.rdn psegs m (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 p) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 FL_ZCALLOC) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 FL_ZCFREE) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -112)) 8 = Some (Z_to_le_bytes 8 0) /\
  OP.rdn psegs m (Z_to_bv 64 p) 8 = Some (Z_to_le_bytes 8 (usp + -192)) /\
  OP.rdn psegs m (Z_to_bv 64 (p + 8)) 4 = Some (Z_to_le_bytes 4 md) /\
  OP.rdn psegs m (Z_to_bv 64 (p + 88)) 8 = Some (Z_to_le_bytes 8 w).

Lemma rdn_same_on8 : forall (P : Z -> Prop) m m' a k bs,
  same_on P m m' -> (forall x, a <= x < a + Z.of_nat k -> P x) -> 0 <= a < 2^64 -> a + Z.of_nat k <= 2^64 ->
  OP.rdn psegs m (Z_to_bv 64 a) k = Some bs -> OP.rdn psegs m' (Z_to_bv 64 a) k = Some bs.
Proof. intros P m m' a k bs SO HP Ha Hk H. rewrite (rdn_same_on P m m' a k SO HP Ha Hk). exact H. Qed.

Lemma IE_CELLS_heap : forall LBp SPc m m' (pp : bptr) p w md,
  rheap_pres LBp SPc m m' -> SPc <= usp + -208 -> In (pp, p, FL_ISTATE_N) LBp -> 0 <= p -> p + FL_ISTATE_N <= 2^64 ->
  IE_CELLS m p w md -> IE_CELLS m' p w md.
Proof.
  intros LBp SPc m m' pp p w md HPR HS Ip Hp Hp2 (E1 & E2 & E3 & E4 & E5 & E6 & E7). pose proof usp_facts as (U1 & U2 & U3 & U4).
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO. unfold IE_CELLS, FL_ISTATE_N in *.
  repeat split.
  all: first [ eapply (rdn_same_on8 _ m m' _ _ _ SO); [| | | eassumption]; [| cbn; lia| cbn; lia];
               first [ intros x Hx; left; cbn in Hx; lia
                     | intros x Hx; right; right; exists (pp, p, 7176); split; [exact Ip| cbn [blk_addr blk_size fst snd]; cbn in Hx; lia] ] ].
Qed.

Lemma L_ic : forall clx s m (pc pu : bptr) (cp up s0v : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID [(pu, up, n); (pc, cp, cl0)] clx s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) -> 0 <= s0v < 2^64 ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -208)) 8 = Some (Z_to_le_bytes 8 s0v) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 0x16204) ->
  implM psegs (REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x2197c) fc1 None m (seg_rom psegs)).
Proof.
  intros clx s m pc pu cp up s0v x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 H TS S0V R1 R2.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR.
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(right; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in Q1, Q2, Q3, Q4, Q5, P1, P2, P3, P4, P5.
  assert (PERM : Permutation.Permutation [(pu, up, n); (pc, cp, cl0)] [(pc, cp, cl0); (pu, up, n)]) by apply Permutation.perm_swap.
  eapply implM_evt with (P := fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x16370) (Z_to_bv 64 (usp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 up) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 cp) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F1 (Z_to_bv 64 0x16370) fc1 None m' (seg_rom psegs)
      /\ MID [(pu, up, n); (pc, cp, cl0)] clx s m' /\ rw_cells psegs m' (usp + -80) (TSSV up cp n)).
  { eapply (fl_seg_ic usp ltac:(lia) _ n cp up s0v lo m F1 fc1); [lia| lia| exact NR| lia| lia| exact S0V| apply (MID_stk_below _ _ _ _ _ H); lia
      | exact (md_mi _ _ _ _ H)| exact R1| exact R2| exact TS|].
    intros M1 MU WM MI1 ST1 RZ TS1. exists M1. split; [reflexivity|]. split; [| exact TS1].
    eapply (MID_munch _ _ s m M1 _ H MU WM MI1). apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
  intros ms' (m' & -> & H' & TS').
  eapply (L_fin1 [] clx s m' F1 fc1 pc pu cp up); [exact (MID_perm _ _ _ _ _ H' PERM)| split; [cbn; lia| constructor]| exact FRM1].
Qed.

Lemma L_zfp : forall clx s m (pp pc pu : bptr) (p cp up s0v : Z)
    (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clx s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) -> 0 <= s0v < 2^64 ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -208)) 8 = Some (Z_to_le_bytes 8 s0v) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 0x16204) ->
  implM psegs (raw_free pp ;;; REST pc pu) s POST
    (MS (mkR (Z_to_bv 64 0x2197c) (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17 x18
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x2397c) fc1 None m (seg_rom psegs)).
Proof.
  intros clx s m pp pc pu p cp up s0v x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 H TS S0V R1 R2.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  destruct (md_err _ _ _ _ H) as [errv ER].
  pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5. unfold FL_ISTATE_N in *.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (pp, p, 7176) :: ([(pu, up, n); (pc, cp, cl0)] ++ LB)) (p := pp) (A := p) (n := 7176) (errv := errv);
      rewrite ?(unsigned_lit (usp + -208)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -208)) in ST' by lia. rewrite ?(unsigned_lit (usp + -208)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove pp ((pp, p, 7176) :: ([(pu, up, n); (pc, cp, cl0)] ++ LB))) with ([(pu, up, n); (pc, cp, cl0)] ++ LB) in HPR, HEAP'
    by (symmetry; apply (RDriver_facts.lb_remove_head (pp, p, 7176)); exact ND).
  assert (H' : MID [(pu, up, n); (pc, cp, cl0)] clx s' m').
  { apply (MID_heap _ [(pu, up, n); (pc, cp, cl0)] _ clx s s' m m' (usp + -208) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_ic clx s' m' pc pu cp up s0v); [exact H'| | exact S0V| |].
  - eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. left. cbn in Ha. lia.
  - eapply (rdn_same_on8 _ m m' _ _ _ SO); [| lia| cbn; lia| exact R1]. intros x Hx; left; cbn in Hx; lia.
  - eapply (rdn_same_on8 _ m m' _ _ _ SO); [| lia| cbn; lia| exact R2]. intros x Hx; left; cbn in Hx; lia.
Qed.

Lemma L_ze1b : forall clx s m (pp pc pu : bptr) (p cp up s0v : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clx s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) -> 0 <= s0v < 2^64 ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -208)) 8 = Some (Z_to_le_bytes 8 s0v) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 0x16204) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 p) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 FL_ZCFREE) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -112)) 8 = Some (Z_to_le_bytes 8 0) ->
  implM psegs (raw_free pp ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x21964) fc1 None m (seg_rom psegs)).
Proof.
  intros clx s m pp pc pu p cp up s0v x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 H TS S0V R1 R2 C1 C2 C3.
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5. unfold FL_ISTATE_N in P3, P4, P5.
  eapply implM_evt with (P := fun ms' => ms' = _);
    [eapply (fl_seg_ze1b usp _ m F1 fc1 p); [lia| exact C1| unfold FL_ZCFREE in C2; exact C2| exact C3| reflexivity]| intros ms' ->].
  eapply (L_zfp clx s m pp pc pu p cp up s0v); [exact H| exact TS| exact S0V| exact R1| exact R2].
Qed.

Lemma L_i4 : forall s m (pw pp pc pu : bptr) (p w md rc3 s0v cp up : Z) (LW : list block)
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  (LW = [] /\ w = 0) \/ (LW = [(pw, w, FL_WIN_N)] /\ w <> 0) ->
  forall clx, MID (LW ++ [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)]) clx s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) -> 0 <= s0v < 2^64 -> 16180 <= md <= 16211 -> (rc3 = -3 \/ rc3 = 1) ->
  IE_CELLS m p w md ->
  implM psegs (HarnessC.inflate_end raw_free pp (match LW with [] => None | _ => Some pw end) ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 s0v) x9 (Z_to_bv 64 rc3) x11 x12 x13 x14 x15 x16 x17 x18
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x161ec) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pw pp pc pu p w md rc3 s0v cp up LW x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 HLW clx H TS S0V MD RC IE.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  destruct (md_err _ _ _ _ H) as [errv ER].
  destruct IE as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  destruct HLW as [[-> ->]|[-> Wnz]]; cbn [app] in *.
  -
    pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
    cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5. unfold FL_ISTATE_N in P3, P4, P5.
    unfold HarnessC.inflate_end.
    eapply implM_evt with (P := fun ms' => exists m' (y14 y15 : word),
        ms' = MS (mkR (Z_to_bv 64 0x2197c) (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9
                     (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 0x1aa04) y14 y15 x16 x17 x18
                     s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F1 (Z_to_bv 64 0x2397c) fc1 None m' (seg_rom psegs)
        /\ MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clx s m' /\ rw_cells psegs m' (usp + -80) (TSSV up cp n)
        /\ OP.rdn psegs m' (Z_to_bv 64 (usp + -208)) 8 = Some (Z_to_le_bytes 8 s0v)
        /\ OP.rdn psegs m' (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 0x16204)).
    { eapply (fl_seg_i4n usp ltac:(lia) SP16 _ p md rc3 s0v lo m F1 fc1); [lia| lia| lia| lia| exact P2| exact MD| exact RC| exact S0V
        | apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)| exact E1| unfold FL_ZCALLOC in E2; exact E2| unfold FL_ZCFREE in E3; exact E3
        | exact E4| exact E5| exact E6| exact E7|].
      intros M1 y13 y15 MU WM MI1 ST1 FR1. exists M1, y13, y15. split; [reflexivity|].
      assert (H1 : MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clx s M1).
      { eapply (MID_munch _ _ s m M1 _ H MU WM MI1). apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      split; [exact H1|]. split.
      - eapply rw_cells_magree; [exact (same_on_munch _ _ _ MU WM)| exact TS|]. intros a Ha. cbn in Ha. cbn. lia.
      - split; [cell_fact FR1 0%nat| cell_fact FR1 8%nat]. }
    intros ms' (m' & y14 & y15 & -> & H' & TS' & R1 & R2).
    eapply (L_zfp clx s m' pp pc pu p cp up s0v); [exact H'| exact TS'| exact S0V| exact R1| exact R2].
  -
    pose proof (MID_blk _ _ _ _ (pw, w, FL_WIN_N) H ltac:(left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
    pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(right; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
    cbn [blk_addr blk_size fst snd] in W1, W2, W3, W4, W5, P1, P2, P3, P4, P5. unfold FL_ISTATE_N, FL_WIN_N in W3, W4, W5, P3, P4, P5.
    unfold HarnessC.inflate_end.
    eapply implM_evt with (P := fun ms' => exists m' (y14 y15 : word),
        ms' = MS (mkR (Z_to_bv 64 0x21964) (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9
                     (Z_to_bv 64 w) (Z_to_bv 64 w) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 0x1aa04) y14 y15 x16 x17 x18
                     s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F1 (Z_to_bv 64 0x2397c) fc1 None m' (seg_rom psegs)
        /\ MID [(pw, w, FL_WIN_N); (pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clx s m' /\ rw_cells psegs m' (usp + -80) (TSSV up cp n)
        /\ OP.rdn psegs m' (Z_to_bv 64 (usp + -208)) 8 = Some (Z_to_le_bytes 8 s0v)
        /\ OP.rdn psegs m' (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 0x16204)
        /\ IE_CELLS m' p w md).
    { eapply (fl_seg_i4w usp ltac:(lia) SP16 _ p w md rc3 s0v lo m F1 fc1); [lia| lia| lia| lia| exact P2| lia| exact MD| exact RC| exact S0V
        | apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)| exact E1| unfold FL_ZCALLOC in E2; exact E2| unfold FL_ZCFREE in E3; exact E3
        | exact E4| exact E5| exact E6| exact E7|].
      intros M1 y13 y15 MU WM MI1 ST1 FR1. exists M1, y13, y15. split; [reflexivity|].
      assert (H1 : MID [(pw, w, FL_WIN_N); (pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clx s M1).
      { eapply (MID_munch _ _ s m M1 _ H MU WM MI1). apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      pose proof (same_on_munch _ _ _ MU WM) as SO.
      split; [exact H1|]. split; [| split; [cell_fact FR1 0%nat| split; [cell_fact FR1 8%nat|]]].
      - eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. cbn in Ha. cbn. lia.
      - unfold IE_CELLS. repeat split.
        all: eapply (rdn_same_on8 _ m M1 _ _ _ SO); [| | | eassumption]; [| cbn; lia| cbn; lia]; intros x Hx; cbn in Hx; cbn; lia. }
    intros ms' (m' & y14 & y15 & -> & H' & TS' & R1 & R2 & IE').
    destruct IE' as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
    destruct (md_err _ _ _ _ H') as [errv' ER'].
    apply implM_bind_assoc. eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := lo) (B := AB) (LB := (pw, w, 32768) :: ([(pp, p, 7176); (pu, up, n); (pc, cp, cl0)] ++ LB)) (p := pw) (A := w) (n := 32768) (errv := errv');
        rewrite ?(unsigned_lit (usp + -208)) by lia.
      - exact (md_heap _ _ _ _ H').
      - left; reflexivity.
      - exact (md_aux _ _ _ _ H').
      - lia.
      - apply (MID_stk_below _ _ _ _ _ H'). lia.
      - exact CEIL.
      - unfold RFREE_STACK. lia.
      - exact ER'.
      - exact (md_mi _ _ _ _ H').
      - exact TP.
      - reflexivity. }
    cbv beta. intros [] s' ms' PO.
    destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m'' & -> & MI' & ST' & ERR'' & AUX' & HPR & FAE & SOE & HEAP').
    rewrite ?(unsigned_lit (usp + -208)) in ST' by lia. rewrite ?(unsigned_lit (usp + -208)) in HPR by lia.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H')) as ND.
    replace (lb_remove pw ((pw, w, 32768) :: ([(pp, p, 7176); (pu, up, n); (pc, cp, cl0)] ++ LB))) with ([(pp, p, 7176); (pu, up, n); (pc, cp, cl0)] ++ LB) in HPR, HEAP'
      by (symmetry; apply (RDriver_facts.lb_remove_head (pw, w, 32768)); exact ND).
    assert (H'' : MID [(pp, p, 7176); (pu, up, n); (pc, cp, cl0)] clx s' m'').
    { apply (MID_heap _ [(pp, p, 7176); (pu, up, n); (pc, cp, cl0)] _ clx s s' m' m'' (usp + -208) H' HPR);
        [intros b Hb; apply in_or_app; right; exact Hb
        | intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
        | lia| exact HEAP'| exact MI'| exact ST'| eexists; exact ERR''| exact AUX'| exact SOE]. }
    pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO'.
    rewrite ret_pc_even by (first [lia| reflexivity]).
    unfold FL_ISTATE_N. eapply (L_ze1b clx s' m'' pp pc pu p cp up s0v); [exact H''| | exact S0V| | | | |].
    + eapply rw_cells_magree; [exact SO'| exact TS'|]. intros a Ha. left. cbn in Ha. lia.
    + eapply (rdn_same_on8 _ m' m'' _ _ _ SO'); [| lia| cbn; lia| exact R1]. intros x Hx; left; cbn in Hx; lia.
    + eapply (rdn_same_on8 _ m' m'' _ _ _ SO'); [| lia| cbn; lia| exact R2]. intros x Hx; left; cbn in Hx; lia.
    + eapply (rdn_same_on8 _ m' m'' _ _ _ SO'); [| lia| cbn; lia| exact J1]. intros x Hx; left; cbn in Hx; lia.
    + eapply (rdn_same_on8 _ m' m'' _ _ _ SO'); [| lia| cbn; lia| exact J3]. intros x Hx; left; cbn in Hx; lia.
    + eapply (rdn_same_on8 _ m' m'' _ _ _ SO'); [| lia| cbn; lia| exact J4]. intros x Hx; left; cbn in Hx; lia.
Qed.

Lemma L_iB : forall s m (pc pu : bptr) (LK : list block) (rc3 s0v cp up : Z) clx
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID (LK ++ [(pu, up, n); (pc, cp, cl0)]) clx s m -> leak_ok LK ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) -> -2^31 <= rc3 < 2^31 -> rc3 <> -3 -> rc3 <> 1 ->
  implM psegs (stderr_fwrite HarnessC.MSG_SHOULD ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 s0v) x9 (Z_to_bv 64 rc3) x11 x12 x13 x14 x15 x16 x17 x18
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x161ec) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pc pu LK rc3 s0v cp up clx x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 H LOK TS RR RA RB.
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  assert (PERM : Permutation.Permutation (LK ++ [(pu, up, n); (pc, cp, cl0)]) ((pc, cp, cl0) :: (pu, up, n) :: LK)).
  { rewrite (Permutation.Permutation_app_comm LK). cbn [app]. apply Permutation.perm_swap. }
  eapply implM_evt with (P := fun ms' => ms' = _);
    [eapply (fl_seg_iB usp ltac:(lia) _ rc3 m F1 fc1); [exact RR| exact RA| exact RB| exact (md_mi _ _ _ _ H)| apply relro_of_hc; exact (md_hc _ _ _ _ H)| reflexivity]
    | intros ms' ->].
  eapply (L_ifw LK clx s m pc pu cp up); [exact (MID_perm _ _ _ _ _ H PERM)| exact LOK| exact TS].
Qed.

Lemma L_fsync : forall s m (pw pp pc pu : bptr) (p w md rc3 cp up : Z) (LW : list block) clx
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  (LW = [] /\ w = 0) \/ (LW = [(pw, w, FL_WIN_N)] /\ w <> 0) ->
  MID (LW ++ [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)]) clx s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) -> 2 <= clx -> -2^31 <= rc3 < 2^31 ->
  ((rc3 = -3 \/ rc3 = 1) -> 16180 <= md <= 16211 /\ IE_CELLS m p w md) ->
  implM psegs (HarnessC.finish_sync raw_free pp (match LW with [] => None | _ => Some pw end) rc3 ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 (clx - 2)) x9 (Z_to_bv 64 rc3) x11 x12 x13 x14 x15 x16 x17 x18
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x161ec) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pw pp pc pu p w md rc3 cp up LW clx x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 HLW H TS CL2 RR CND.
  pose proof (md_clx _ _ _ _ H) as CLX.
  unfold HarnessC.finish_sync, ZE_DATA_ERROR, ZE_STREAM_END.
  destruct (Z.eqb_spec rc3 (-3)) as [E3|N3]; [| destruct (Z.eqb_spec rc3 1) as [E1|N1]]; cbn [orb].
  - destruct (CND (or_introl E3)) as [MD IE].
    eapply (L_i4 s m pw pp pc pu p w md rc3 (clx - 2) cp up LW); [exact HLW| exact H| exact TS| lia| exact MD| left; exact E3| exact IE].
  - destruct (CND (or_intror E1)) as [MD IE].
    eapply (L_i4 s m pw pp pc pu p w md rc3 (clx - 2) cp up LW); [exact HLW| exact H| exact TS| lia| exact MD| right; exact E1| exact IE].
  -
    replace (LW ++ [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)]) with ((LW ++ [(pp, p, FL_ISTATE_N)]) ++ [(pu, up, n); (pc, cp, cl0)]) in H
      by (rewrite <- app_assoc; reflexivity).
    eapply (L_iB s m pc pu (LW ++ [(pp, p, FL_ISTATE_N)]) rc3 (clx - 2) cp up clx); [exact H| | exact TS| exact RR| exact N3| exact N1].
    destruct HLW as [[-> _]|[-> _]]; cbn [app]; (split; [cbn; lia|]); unfold FL_ISTATE_N, FL_WIN_N, HarnessC.ISTATE_N, HarnessC.WIN_N;
      repeat (apply Forall_cons; [cbn [blk_size fst snd]; first [left; reflexivity| right; reflexivity]|]); apply Forall_nil.
Qed.

Lemma clen_range : 2 <= clen <= cl0.
Proof. pose proof (fm_clen_range FLM payload) as X. unfold zlength. exact X. Qed.
Lemma t_mod8 : (usp + -192) mod 8 = 0.
Proof. pose proof SP16 as X. apply Z.mod_divide in X; [|lia]. destruct X as [k Hk]. rewrite Hk. replace (k * 16 + -192) with ((2 * k - 24) * 8) by lia. apply Z_mod_mult. Qed.
Lemma t_mod16 : (usp + -192) mod 16 = 0.
Proof. replace (usp + -192) with (usp + (-12) * 16) by lia. rewrite Z_mod_plus_full. exact SP16. Qed.
Lemma cmp_len : Z.of_nat (length cmp) = cl0.
Proof. pose proof (fm_compr_len FLM payload) as X. unfold zlength. exact X. Qed.

Lemma holds_slice : forall m a l k j,
  bytes_at psegs m a (map (Z_to_bv 8) l) -> 0 <= k -> 0 <= j -> k + j <= Z.of_nat (length l) ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m (a + k) (firstn (Z.to_nat j) (skipn (Z.to_nat k) l)).
Proof.
  intros m a l k j BY Hk Hj Hkj.
  pose proof (bytes_at_rdn psegs m a (map (Z_to_bv 8) l) (Z.to_nat k) (Z.to_nat j) BY ltac:(rewrite length_map; lia)) as X.
  unfold wa in X. rewrite Z2Nat.id in X by lia. rewrite List.skipn_map, List.firstn_map in X.
  unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds. rewrite length_firstn, length_skipn, Nat.min_l by lia. rewrite <- rdn_conv in X. exact X.
Qed.
Lemma slice_length : forall (l : list Z) k j, 0 <= k -> 0 <= j -> k + j <= Z.of_nat (length l) ->
  ZI.zlength (firstn (Z.to_nat j) (skipn (Z.to_nat k) l)) = j.
Proof. intros l k j Hk Hj Hkj. unfold ZI.zlength. rewrite length_firstn, length_skipn, Nat.min_l by lia. lia. Qed.

Lemma cell4_same_on : forall (P : Z -> Prop) m m' a v,
  same_on P m m' -> (forall x, a <= x < a + 4 -> P x) -> 0 <= a -> a + 4 <= 2^64 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m a v -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m' a v.
Proof. intros P m m' a v SO HP Ha H4 H. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 in *. rewrite <- ?rdn_conv in *. rewrite (rdn_same_on P m m' a 4 SO); [exact H| exact HP| lia| cbn; lia]. Qed.

Lemma izs_same_on : forall (P : Z -> Prop) m m' inp ai outp ao z p,
  same_on P m m' -> (forall x, usp - 192 <= x < usp - 88 -> P x) ->
  izs_cells (fl_msga CT1) m (usp + -192) inp ai outp ao z p FL_ZCALLOC FL_ZCFREE ->
  izs_cells (fl_msga CT1) m' (usp + -192) inp ai outp ao z p FL_ZCALLOC FL_ZCFREE.
Proof.
  intros P m m' inp ai outp ao z p SO HP (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96).
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  unfold izs_cells. repeat split.
  all: first [ eapply (cell8_same_on P m m'); [exact SO| | | | eassumption]; [| lia| lia]; intros x Hx; apply HP; lia
             | eapply (cell4_same_on P m m'); [exact SO| | | | eassumption]; [| lia| lia]; intros x Hx; apply HP; lia ].
Qed.

Lemma IE_of_strm : forall m p w inp ai outp ao z si,
  izs_cells (fl_msga CT1) m (usp + -192) inp ai outp ao z p FL_ZCALLOC FL_ZCFREE -> fl_irep CT1 m (IP (usp + -192) p w) si ->
  IE_CELLS m p w (ZIS.is_mode si) /\ 16180 <= ZIS.is_mode si <= 16211.
Proof.
  intros m p w inp ai outp ao z si (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96) IR.
  destruct (fl_irep_cells CT1 _ _ _ IR) as (P0 & P8 & MR & P72). cbn [ip_p ip_strm ip_w] in P0, P8, MR, P72.
  unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 in *.
  replace (usp + -192 + 56) with (usp + -136) in C56 by lia. replace (usp + -192 + 64) with (usp + -128) in C64 by lia.
  replace (usp + -192 + 72) with (usp + -120) in C72 by lia. replace (usp + -192 + 80) with (usp + -112) in C80 by lia.
  split; [| exact MR]. unfold IE_CELLS. repeat split; assumption.
Qed.

Lemma TW_heap : forall LBp SPc m m' (pp pc pu : bptr) (p cp up inp outp : Z) (R0 RW : bvmap 5 word) si zc f,
  rheap_pres LBp SPc m m' -> SPc <= usp - 192 - 320 -> stk psegs m' lo usp ->
  In (pp, p, FL_ISTATE_N) LBp -> In (pc, cp, cl0) LBp -> In (pu, up, n) LBp ->
  OP.getr R0 2 = Z_to_bv 64 (usp + -192) ->
  cp <= inp -> inp + ZI.zlength (ZI.zc_input zc) <= cp + cl0 -> up <= outp -> outp + ZI.zc_avail_out zc <= up + n ->
  fl_tw CT1 R0 RW (IP (usp + -192) p 0) inp outp si zc f m -> fl_tw CT1 R0 RW (IP (usp + -192) p 0) inp outp si zc f m'.
Proof.
  intros LBp SPc m m' pp pc pu p cp up inp outp R0 RW si zc f HPR HS STK Ip Ic Iu G2 I1 I2 O1 O2 TW.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  apply (fl_tw_local CT1 R0 RW (IP (usp + -192) p 0) inp outp si zc f m m'); [| | exact TW].
  - cbv zeta. rewrite G2. rewrite unsigned_lit by lia. cbn [ip_p ip_strm]. unfold FL_ZWD, FL_ISTATE_N.
    intros a IN. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with (2^64) in RA.
    assert (CA : rclient_addr LBp SPc (bv_unsigned a)).
    { destruct IN as [IN|[IN|[IN|[IN|IN]]]].
      - left. lia.
      - right; right. exists (pp, p, FL_ISTATE_N). split; [exact Ip|]. cbn [blk_addr blk_size fst snd]. unfold FL_ISTATE_N. lia.
      - left. lia.
      - right; right. exists (pu, up, n). split; [exact Iu|]. cbn [blk_addr blk_size fst snd]. lia.
      - right; right. exists (pc, cp, cl0). split; [exact Ic|]. cbn [blk_addr blk_size fst snd]. lia. }
    destruct (HPR (bv_unsigned a) RA CA) as [E _]. unfold wa in E. rewrite (Z_to_bv_bv_unsigned a) in E. exact E.
  -
    cbv zeta. rewrite G2. rewrite unsigned_lit by lia. unfold FL_FRA, FL_ZWD.
    intros a Ha. destruct STK as (_ & _ & SK). destruct (SK (bv_unsigned a) ltac:(lia)) as [W _].
    unfold wa in W. rewrite (Z_to_bv_bv_unsigned a) in W. unfold wview in W.
    rewrite (ref_find_segment_none (bv_unsigned a) 1) in W by lia.
    destruct (m' a); [discriminate | exact W].
Qed.

Lemma leak_ok_p : forall (pp : bptr) p, leak_ok [(pp, p, FL_ISTATE_N)].
Proof. intros pp p. split; [cbn; lia|]. apply Forall_cons; [left; reflexivity| apply Forall_nil]. Qed.

Lemma rc3_range : In (ZI.zr_rc cIR3) INFL_RCS -> -2^31 <= ZI.zr_rc cIR3 < 2^31.
Proof. intros H. apply INFL_RCS_range in H. lia. Qed.

Lemma L_inb : forall s m (pw pp pc pu : bptr) (p w cp up : Z)
    (e5 e6 e7 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31 : word)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (z1 z5 z6 z7 z14 z15 z16 z17 z28 z29 z30 z31 : word),
  let R0 := mkR (Z_to_bv 64 0x161ec) (Z_to_bv 64 (usp + -192)) gp tp e5 e6 e7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 4)
                e12 e13 e14 e15 e16 e17 (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 e28 e29 e30 e31 in
  let RW := mkR z1 (Z_to_bv 64 (usp + -192 - 320)) gp tp z5 z6 z7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 FL_ZCALLOC)
                z14 z15 z16 z17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 z28 z29 z30 z31 in
  MID [(pw, w, FL_WIN_N); (pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  0 <= cICONS1 <= 2 -> 0 <= cICONS2 <= clen - 2 -> 0 <= cINOUT1 <= n ->
  fl_tw CT1 R0 RW (IP (usp + -192) p 0) (cp + (cICONS1 + cICONS2)) (up + cINOUT1) cIS2 cIZC3 4 m ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m w FL_WIN_N ->
  snd cICALL3 = Some 32768 ->
  implM psegs (HarnessC.finish_sync raw_free pp (Some pw) (fm_i2b FLM cmp clen n) ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192 - 320)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 w) x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F1 (Z_to_bv 64 FL_A_ZB) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pw pp pc pu p w cp up e5 e6 e7 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31
         x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         z1 z5 z6 z7 z14 z15 z16 z17 z28 z29 z30 z31 R0 RW H TS CU1 CU2 CU3 TW ZW ASK.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof clen_range as CLN. pose proof cmp_len as CML. assert (ZN : ZI.zlength payload = n) by reflexivity. pose proof atop_range as AR.
  pose proof (MID_blk _ _ _ _ (pw, w, FL_WIN_N) H ltac:(left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(right; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 2 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 3 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in W1, W2, W3, W4, W5, P1, P2, P3, P4, P5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5.
  unfold FL_WIN_N, FL_ISTATE_N in W3, W4, W5, P3, P4, P5.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP. cbn [rev map app blk_addr blk_size fst snd] in AP.
  unfold FL_WIN_N, FL_ISTATE_N in AP. destruct AP as (_ & (AK1 & AK2 & AK3 & _) & (AQ1 & AQ2 & _) & (AP1 & _) & _). unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in AK1, AK2, AK3, AQ1, AQ2, AP1.
  pose proof (slice_length cmp (cICONS1 + cICONS2) (clen - 2 - cICONS2) ltac:(blia) ltac:(blia) ltac:(blia)) as LEN3.
  assert (RCS : In (ZI.zr_rc cIR3) INFL_RCS).
  { rewrite <- (lk_i2b _ _ _ _ LNK1 ltac:(rewrite ASK; discriminate)). apply fm_i2b_rcs. }
  pose proof (rc3_range RCS) as RR.
  rewrite (lk_i2b _ _ _ _ LNK1 ltac:(rewrite ASK; discriminate)).
  eapply implM_evt with (P := fun ms' => exists m' (nout : Z) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      0 <= nout <= n - cINOUT1 /\
      OF.frame_mod m m' [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 (up + cINOUT1), nout);
                         (Z_to_bv 64 p, 7176); (Z_to_bv 64 w, 32768)] /\
      (~ InflateRc.RR (ZI.zr_rc cIR3) ->
         fl_irep CT1 m' (IP (usp + -192) p w) cIS3 /\
         izs_cells (fl_msga CT1) m' (usp + -192) (cp + (cICONS1 + cICONS2) + ZI.zr_consumed cIR3) (ZI.zlength (ZI.zc_input cIZC3) - ZI.zr_consumed cIR3)
                   (up + cINOUT1 + nout) (n - cINOUT1 - nout) (ZI.zr_strm cIR3) p FL_ZCALLOC FL_ZCFREE) /\
      ms' = MS (mkR y1 (Z_to_bv 64 (usp + -192)) gp tp y5 y6 y7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 (ZI.zr_rc cIR3)) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F1 (Z_to_bv 64 0x161ec) fc1 None m' (seg_rom psegs)).
  { eapply (inb_evt FLIB F1 fc1 _ m (usp + -192) p w (usp + -192) 0x161ec (cp + (cICONS1 + cICONS2)) (up + cINOUT1) ATOP 4 cIS2 cIZC3 WB RW).
    - exact TW.
    - subst RW. unfold OL.rkeep, OL.FL_KEEP. intros k Hk. cbn in Hk.
      repeat (destruct Hk as [<-|Hk]; [reflexivity|]). destruct Hk.
    - lia.
    - lia.
    - exact (MID_ro _ _ _ _ H).
    - exact (blk_okz_of_MID _ _ _ _ pw w 32768 H ltac:(left; reflexivity)).
    - exact ZW.
    - rewrite LEN3. cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.iblocks OL.ip_p OL.ip_w Z.eqb ZI.zc_avail_out cIZC3 IZC3]. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_ISTATE_N.
      repeat split; blia.
    - exact ASK.
    - intros m' nout y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 NO FM GRD.
      exists m', nout, y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      split; [exact NO|]. split.
      { unfold OL.iblocks, OL.wz in FM. cbn [OL.ip_p OL.ip_w OL.ip_strm map fst snd app] in FM.
        rewrite (proj2 (Z.eqb_neq w 0) ltac:(lia)) in FM. cbn [map fst snd app] in FM.
        replace (usp + -192 - FL_IFR) with (usp + -192 - 464) in FM by reflexivity. exact FM. }
      split; [| reflexivity]. intros NRR. destruct (GRD NRR) as (_ & _ & IR' & ZS' & _).
      split; [exact IR'|]. replace (n - cINOUT1 - nout) with (ZI.zc_avail_out cIZC3 - nout) by reflexivity. exact ZS'. }
  intros ms' (m' & nout & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & NO & FM & GRD & ->).
  assert (FPOK : Forall (fp_ok [(pw, w, 32768); (pp, p, 7176); (pu, up, n); (pc, cp, cl0)])
             (fm_ivs [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 (up + cINOUT1), nout);
                      (Z_to_bv 64 p, 7176); (Z_to_bv 64 w, 32768)])).
  { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by blia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; exists (pu, up, n); split; [do 2 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pp, p, 7176); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pw, w, 32768); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_nil. }
  pose proof (MID_fm _ _ s m m' _ H FM FPOK) as H'.
  pose proof (same_on_frame_mod _ _ _ FM) as SO.
  assert (TS' : rw_cells psegs m' (usp + -80) (TSSV up cp n)).
  { eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. cbn in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by blia. blia. }
  eapply (L_fsync s m' pw pp pc pu p w (ZIS.is_mode cIS3) (ZI.zr_rc cIR3) cp up [(pw, w, FL_WIN_N)] clen);
    [right; split; [reflexivity| lia]| exact H'| exact TS'| lia| exact RR|].
  intros E31. destruct (GRD ltac:(unfold InflateRc.RR, ZI.Z_NEED_DICT, ZI.Z_MEM_ERROR, ZI.Z_STREAM_ERROR; blia)) as [IR' ZS'].
  destruct (IE_of_strm m' p w _ _ _ _ _ cIS3 ZS' IR') as [IE MR]. split; [exact MR| exact IE].
Qed.

Lemma L_zw : forall s m (pp pc pu : bptr) (p cp up : Z)
    (e5 e6 e7 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31 : word)
    (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R0 := mkR (Z_to_bv 64 0x161ec) (Z_to_bv 64 (usp + -192)) gp tp e5 e6 e7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 4)
                e12 e13 e14 e15 e16 e17 (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 e28 e29 e30 e31 in
  MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  0 <= cICONS1 <= 2 -> 0 <= cICONS2 <= clen - 2 -> 0 <= cINOUT1 <= n ->
  fl_tw CT1 R0 (mkR x1 (Z_to_bv 64 (usp + -192 - 320)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 FL_ZCALLOC)
                  x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (IP (usp + -192) p 0) (cp + (cICONS1 + cICONS2)) (up + cINOUT1) cIS2 cIZC3 4 m ->
  snd cICALL3 = Some 32768 ->
  implM psegs ((wd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.WIN_N ;; HarnessC.finish_sync raw_free pp (Some wd) (fm_i2b FLM cmp clen n)) ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192 - 320)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 FL_ZCALLOC)
             x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F1 (Z_to_bv 64 FL_A_ZW) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pp pc pu p cp up e5 e6 e7 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31
         x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 R0 H TS CU1 CU2 CU3 TW ASK.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof clen_range as CLN. pose proof cmp_len as CML. assert (ZN : ZI.zlength payload = n) by reflexivity.
  destruct (md_err _ _ _ _ H) as [errv ER].
  pose proof (slice_length cmp (cICONS1 + cICONS2) (clen - 2 - cICONS2) ltac:(lia) ltac:(lia) ltac:(lia)) as LEN3.
  unfold FL_A_ZW, FL_ZCALLOC, HarnessC.WIN_N. apply implM_bind_assoc.
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply fl_seg_zw; reflexivity| intros ms' ->].
  eapply implM_zreq.
  { unfold rmalloc_stmt_z in MALLOCZ.
    eapply MALLOCZ with (lo := lo) (B := AB) (LB := [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] ++ LB) (n := 32768) (errv := errv);
      rewrite ?(unsigned_lit (usp + -192 - 320)) by lia.
    - exact (md_heap _ _ _ _ H).
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros pw s' ms' PO FRSH.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -192 - 320)) in ST' by lia. rewrite ?(unsigned_lit (usp + -192 - 320)) in HPR by lia.
  destruct RES as (A & junk & -> & BR & HEAP' & BLK & _ & ZJ). specialize (ZJ FRSH). subst junk.
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ 32768 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(pw, A, FL_WIN_N); (pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s' m').
  { apply (MID_heap _ _ _ clen s s' m m' (usp + -192 - 320) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (TW_heap _ _ m m' pp pc pu p cp up (cp + (cICONS1 + cICONS2)) (up + cINOUT1) R0 _ cIS2 cIZC3 4 HPR ltac:(lia) (md_stk _ _ _ _ H')
                ltac:(left; reflexivity) ltac:(do 2 right; left; reflexivity) ltac:(right; left; reflexivity) eq_refl
                ltac:(lia) ltac:(rewrite LEN3; lia) ltac:(lia) ltac:(cbn [ZI.zc_avail_out cIZC3 IZC3]; lia) TW) as TW'.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_inb s' m' pw pp pc pu p A cp up e5 e6 e7 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31);
    [exact H'| | exact CU1| exact CU2| exact CU3| exact TW'| apply (zeros_at_of_chunk m' A 32768 BLK); lia| exact ASK].
  eapply rw_cells_magree; [exact (same_on_rheap_pres _ _ _ _ HPR)| exact TS|]. intros a Ha. left. cbn in Ha. lia.
Qed.

Lemma L_inf3 : forall s m (pp pc pu : bptr) (p cp up : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  0 <= cICONS1 <= 2 -> 0 <= cICONS2 <= clen - 2 -> 0 <= cINOUT1 <= n ->
  fl_irep CT1 m (IP (usp + -192) p 0) cIS2 -> ZIS.is_window_blk cIS2 = None ->
  izs_cells (fl_msga CT1) m (usp + -192) (cp + (cICONS1 + cICONS2)) (clen - 2 - cICONS2) (up + cINOUT1) (n - cINOUT1) (ZI.zr_strm cIR2) p FL_ZCALLOC FL_ZCFREE ->
  bytes_at psegs m cp (map (Z_to_bv 8) cmp) -> ZI.zr_rc cIR1 = ZI.Z_OK -> ZI.zr_rc cIR2 = ZI.Z_OK ->
  implM psegs (match fm_i2 FLM cmp clen n with
               | I2_R rc3 => HarnessC.finish_sync raw_free pp None rc3
               | I2_W => wd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.WIN_N ;; HarnessC.finish_sync raw_free pp (Some wd) (fm_i2b FLM cmp clen n)
               end ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x161dc) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pp pc pu p cp up x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TS CU1 CU2 CU3 IR WIN2 ZS BY RC1 RC2.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof clen_range as CLN. pose proof cmp_len as CML. assert (ZN : ZI.zlength payload = n) by reflexivity. pose proof atop_range as AR.
  pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 2 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5. unfold FL_ISTATE_N in P3, P4, P5.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP. cbn [rev map app blk_addr blk_size fst snd] in AP.
  unfold FL_ISTATE_N in AP. destruct AP as (_ & (AK1 & AK2 & _) & (AQ1 & _) & _). unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in AK1, AK2, AQ1.
  pose proof (slice_length cmp (cICONS1 + cICONS2) (clen - 2 - cICONS2) ltac:(lia) ltac:(lia) ltac:(lia)) as LEN3.
  pose proof (holds_slice m cp cmp (cICONS1 + cICONS2) (clen - 2 - cICONS2) BY ltac:(lia) ltac:(lia) ltac:(lia)) as HLD.
  rewrite (lk_i2 _ _ _ _ LNK1).
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply fl_seg_i3; reflexivity| intros ms' ->].
  set (R0 := mkR (Z_to_bv 64 0x161ec) (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 4)
                 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31).
  destruct (snd cICALL3) as [sz|] eqn:ASK.
  -
    eapply implM_evt with (P := fun ms' => exists m' (nout : Z) (y1 y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
        0 <= nout <= n - cINOUT1 /\
        OF.frame_mod m m' [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 (up + cINOUT1), nout); (Z_to_bv 64 p, 7176)] /\
        fl_tw CT1 R0 (mkR y1 (Z_to_bv 64 (usp + -192 - 320)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 FL_ZCALLOC)
                        y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          (IP (usp + -192) p 0) (cp + (cICONS1 + cICONS2)) (up + cINOUT1) cIS2 cIZC3 4 m' /\ sz = 32768 /\
        ms' = MS (mkR y1 (Z_to_bv 64 (usp + -192 - 320)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 FL_ZCALLOC)
                       y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F1 (Z_to_bv 64 FL_A_ZW) fc1 None m' (seg_rom psegs)).
    + eapply (inf_evt FLIB F1 fc1 _ m (usp + -192) p 0 (usp + -192) 0x161ec (cp + (cICONS1 + cICONS2)) (up + cINOUT1) ATOP 4 cIS2 cIZC3 (WANS WB)).
      * split; [lia| reflexivity].
      * apply t_mod16.
      * lia.
      * lia.
      * lia.
      * unfold OL.blocks_ok, OL.iblocks. cbn [OL.ip_p OL.ip_w Z.eqb app]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        exact (blk_okz_of_MID _ _ _ _ pp p 7176 H ltac:(left; reflexivity)).
      * exact (MID_ro _ _ _ _ H).
      * lia.
      * lia.
      * apply t_mod8.
      * lia.
      * lia.
      * unfold wa. apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ _ H)| lia| lia].
      * apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
      * cbn [ZI.zc_avail_out cIZC3 IZC3].
        pose proof (wr_at_store_ok psegs m up n cINOUT1 (Z.to_nat (n - cINOUT1)) (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) (pu, up, n) ltac:(right; left; reflexivity)) ltac:(lia) ltac:(lia)) as X. exact X.
      * rewrite LEN3. cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.iblocks OL.ip_p OL.ip_w Z.eqb ZI.zc_avail_out cIZC3 IZC3 app]. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_ISTATE_N.
        repeat split; lia.
      * rewrite LEN3. cbn [ZI.zc_avail_out cIZC3 IZC3]. intros a k Hin. cbn in Hin.
        destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
      * rewrite LEN3. lia.
      * cbn [ZI.zc_avail_out cIZC3 IZC3]. lia.
      * cbn [ZI.zc_avail_out cIZC3 IZC3]. lia.
      * rewrite LEN3. lia.
      * exact IR.
      * split; [intros _; exact WIN2| intros _; reflexivity].
      * exact HLD.
      * rewrite LEN3. exact ZS.
      * exact (lk_isf3 _ _ _ _ LNK1 RC1 RC2).
      * intros m' nout y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 ASK'. exfalso. rewrite ASK in ASK'. discriminate.
      * intros m' nout y1 y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ASK' _ NO FM TW.
        rewrite ASK in ASK'. injection ASK' as ->.
        exists m', nout, y1, y5, y6, y7, y8, y9, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31.
        split; [exact NO|]. split.
        { unfold OL.iblocks, OL.wz in FM. cbn [OL.ip_p OL.ip_w OL.ip_strm map fst snd app Z.eqb] in FM.
          replace (usp + -192 - FL_IFR) with (usp + -192 - 464) in FM by reflexivity. exact FM. }
        split; [exact TW|]. split; [reflexivity| reflexivity].
    + intros ms' (m' & nout & y1 & y5 & y6 & y7 & y8 & y9 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31
                   & NO & FM & TW & -> & ->).
      assert (FPOK : Forall (fp_ok [(pp, p, 7176); (pu, up, n); (pc, cp, cl0)])
                 (fm_ivs [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 (up + cINOUT1), nout); (Z_to_bv 64 p, 7176)])).
      { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [right; exists (pu, up, n); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
        apply Forall_cons; [right; exists (pp, p, 7176); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
        apply Forall_nil. }
      pose proof (MID_fm _ _ s m m' _ H FM FPOK) as H'.
      assert (TS' : rw_cells psegs m' (usp + -80) (TSSV up cp n)).
      { eapply rw_cells_magree; [exact (same_on_frame_mod _ _ _ FM)| exact TS|]. intros a Ha. cbn in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
      apply (L_zw s m' pp pc pu p cp up x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31); [exact H'| exact TS'| exact CU1| exact CU2| exact CU3| exact TW| exact ASK].
  -
    eapply implM_evt with (P := fun ms' => exists m' (nout : Z) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        0 <= nout <= n - cINOUT1 /\
        OF.frame_mod m m' [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 (up + cINOUT1), nout); (Z_to_bv 64 p, 7176)] /\
        (~ InflateRc.RR (ZI.zr_rc cIR3) ->
           fl_irep CT1 m' (IP (usp + -192) p 0) cIS3 /\
           izs_cells (fl_msga CT1) m' (usp + -192) (cp + (cICONS1 + cICONS2) + ZI.zr_consumed cIR3) (ZI.zlength (ZI.zc_input cIZC3) - ZI.zr_consumed cIR3)
                     (up + cINOUT1 + nout) (n - cINOUT1 - nout) (ZI.zr_strm cIR3) p FL_ZCALLOC FL_ZCFREE) /\
        ms' = MS (mkR y1 (Z_to_bv 64 (usp + -192)) gp tp y5 y6 y7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 (ZI.zr_rc cIR3)) y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F1 (Z_to_bv 64 0x161ec) fc1 None m' (seg_rom psegs)).
    + eapply (inf_evt FLIB F1 fc1 _ m (usp + -192) p 0 (usp + -192) 0x161ec (cp + (cICONS1 + cICONS2)) (up + cINOUT1) ATOP 4 cIS2 cIZC3 (WANS WB)).
      * split; [lia| reflexivity].
      * apply t_mod16.
      * lia.
      * lia.
      * lia.
      * unfold OL.blocks_ok, OL.iblocks. cbn [OL.ip_p OL.ip_w Z.eqb app]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        exact (blk_okz_of_MID _ _ _ _ pp p 7176 H ltac:(left; reflexivity)).
      * exact (MID_ro _ _ _ _ H).
      * lia.
      * lia.
      * apply t_mod8.
      * lia.
      * lia.
      * unfold wa. apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ _ H)| lia| lia].
      * apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
      * cbn [ZI.zc_avail_out cIZC3 IZC3].
        pose proof (wr_at_store_ok psegs m up n cINOUT1 (Z.to_nat (n - cINOUT1)) (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) (pu, up, n) ltac:(right; left; reflexivity)) ltac:(lia) ltac:(lia)) as X. exact X.
      * rewrite LEN3. cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.iblocks OL.ip_p OL.ip_w Z.eqb ZI.zc_avail_out cIZC3 IZC3 app]. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_ISTATE_N.
        repeat split; lia.
      * rewrite LEN3. cbn [ZI.zc_avail_out cIZC3 IZC3]. intros a k Hin. cbn in Hin.
        destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
      * rewrite LEN3. lia.
      * cbn [ZI.zc_avail_out cIZC3 IZC3]. lia.
      * cbn [ZI.zc_avail_out cIZC3 IZC3]. lia.
      * rewrite LEN3. lia.
      * exact IR.
      * split; [intros _; exact WIN2| intros _; reflexivity].
      * exact HLD.
      * rewrite LEN3. exact ZS.
      * exact (lk_isf3 _ _ _ _ LNK1 RC1 RC2).
      * intros m' nout y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 _ NO FM GRD.
        exists m', nout, y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
        split; [exact NO|]. split.
        { unfold OL.iblocks, OL.wz in FM. cbn [OL.ip_p OL.ip_w OL.ip_strm map fst snd app Z.eqb] in FM.
          replace (usp + -192 - FL_IFR) with (usp + -192 - 464) in FM by reflexivity. exact FM. }
        split; [| reflexivity]. intros NRR. destruct (GRD NRR) as (_ & _ & IR' & ZS' & _).
        split; [exact IR'|]. replace (n - cINOUT1 - nout) with (ZI.zc_avail_out cIZC3 - nout) by reflexivity. exact ZS'.
      * intros m' nout y1 y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ASK'. exfalso. rewrite ASK in ASK'. discriminate.
    + intros ms' (m' & nout & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & NO & FM & GRD & ->).
      assert (FPOK : Forall (fp_ok [(pp, p, 7176); (pu, up, n); (pc, cp, cl0)])
                 (fm_ivs [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 (up + cINOUT1), nout); (Z_to_bv 64 p, 7176)])).
      { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [right; exists (pu, up, n); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
        apply Forall_cons; [right; exists (pp, p, 7176); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
        apply Forall_nil. }
      pose proof (MID_fm _ _ s m m' _ H FM FPOK) as H'.
      pose proof (same_on_frame_mod _ _ _ FM) as SO.
      assert (TS' : rw_cells psegs m' (usp + -80) (TSSV up cp n)).
      { eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. cbn in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
      assert (RCS : In (ZI.zr_rc cIR3) INFL_RCS).
      { apply (fm_i2_rcs FLM cmp clen n). rewrite (lk_i2 _ _ _ _ LNK1), ASK. reflexivity. }
      eapply (L_fsync s m' pp pp pc pu p 0 (ZIS.is_mode cIS3) (ZI.zr_rc cIR3) cp up [] clen);
        [left; split; reflexivity| exact H'| exact TS'| lia| exact (rc3_range RCS)|].
      intros E31. destruct (GRD ltac:(unfold InflateRc.RR, ZI.Z_NEED_DICT, ZI.Z_MEM_ERROR, ZI.Z_STREAM_ERROR; lia)) as [IR' ZS'].
      destruct (IE_of_strm m' p 0 _ _ _ _ _ cIS3 ZS' IR') as [IE MR]. split; [exact MR| exact IE].
Qed.

Lemma irep_munch : forall W m m1 p si,
  fl_irep CT1 m (IP (usp + -192) p 0) si -> munch W m m1 -> wmono psegs m m1 ->
  (forall x, p <= x < p + 7176 -> outside W x) -> fl_irep CT1 m1 (IP (usp + -192) p 0) si.
Proof.
  intros W m m1 p si IR MU WM HO. apply (fl_irep_frame CT1 m m1 _ si IR).
  intros a b k Hin Ha. unfold iblocks in Hin. cbn [ip_p ip_w Z.eqb app] in Hin. destruct Hin as [E|[]]. injection E as <- <-.
  apply MU. apply HO. unfold FL_ISTATE_N in Ha. lia.
Qed.

Lemma L_isy : forall s m (pp pc pu : bptr) (p cp up : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  0 <= cICONS1 <= 2 -> 0 <= cINOUT1 <= n ->
  fl_irep CT1 m (IP (usp + -192) p 0) cIS1 -> ZIS.is_window_blk cIS1 = None ->
  izs_cells (fl_msga CT1) m (usp + -192) (cp + cICONS1) (2 - cICONS1) (up + cINOUT1) (n - cINOUT1) (ZI.zr_strm cIR1) p FL_ZCALLOC FL_ZCFREE ->
  bytes_at psegs m cp (map (Z_to_bv 8) cmp) -> ZI.zr_rc cIR1 = ZI.Z_OK ->
  implM psegs (match fm_is FLM cmp clen n with
               | IS_E e => HarnessC.diag_zerr HarnessC.MSG_INFLATESYNC e
               | IS_OK => match fm_i2 FLM cmp clen n with
                          | I2_R rc3 => HarnessC.finish_sync raw_free pp None rc3
                          | I2_W => wd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.WIN_N ;; HarnessC.finish_sync raw_free pp (Some wd) (fm_i2b FLM cmp clen n)
                          end
               end ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 clen) (Z_to_bv 64 n) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x161c8) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pp pc pu p cp up x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TS CU1 CU3 IR WIN1 ZS BY RC1.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof clen_range as CLN. pose proof cmp_len as CML. assert (ZN : ZI.zlength payload = n) by reflexivity. pose proof atop_range as AR. pose proof (md_clx _ _ _ _ H) as CLX.
  pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 2 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5. unfold FL_ISTATE_N in P3, P4, P5.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP. cbn [rev map app blk_addr blk_size fst snd] in AP.
  unfold FL_ISTATE_N in AP. destruct AP as (_ & (AK1 & AK2 & _) & (AQ1 & _) & _). unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in AK1, AK2, AQ1.
  pose proof (slice_length cmp cICONS1 (clen - 2) ltac:(lia) ltac:(lia) ltac:(lia)) as LEN2.
  eapply implM_evt with (P := fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 0x161dc) (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 (usp + -192)) x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F1 (Z_to_bv 64 0x21998) fc1 None m1 (seg_rom psegs)
      /\ MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m1 /\ rw_cells psegs m1 (usp + -80) (TSSV up cp n)
      /\ fl_irep CT1 m1 (IP (usp + -192) p 0) cIS1
      /\ izs_cells (fl_msga CT1) m1 (usp + -192) (cp + cICONS1) (clen - 2) (up + cINOUT1) (n - cINOUT1) (ZI.zr_strm cIR1) p FL_ZCALLOC FL_ZCFREE
      /\ bytes_at psegs m1 cp (map (Z_to_bv 8) cmp)).
  { eapply (fl_seg_i2 usp _ n up clen lo m F1 fc1); [lia| lia| exact NR| lia| lia| apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)|].
    intros M1 MU WM MI1 ST1 RAI. exists M1. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    split; [eapply (MID_munch _ _ s m M1 _ H MU WM MI1); apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]|].
    split; [eapply rw_cells_magree; [exact SO| exact TS|]; intros a Ha; cbn in Ha; cbn; lia|].
    split; [apply (irep_munch _ m M1 p cIS1 IR MU WM); intros x Hx; cbn; lia|].
    split.
    - destruct ZS as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96). unfold izs_cells.
      split; [eapply (cell8_same_on _ m M1); [exact SO| intros x Hx; cbn; lia| lia| lia| exact C0]|].
      split; [unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4; replace (usp + -192 + 8) with (usp + -184) by lia; exact RAI|].
      repeat split.
      all: first [ eapply (cell8_same_on _ m M1); [exact SO| | | | eassumption]; [intros x Hx; cbn; lia| lia| lia]
                 | eapply (cell4_same_on _ m M1); [exact SO| | | | eassumption]; [intros x Hx; cbn; lia| lia| lia] ].
    - eapply bytes_at_magree; [exact SO| exact BY|]. intros a Ha. rewrite length_map in Ha. cbn. lia. }
  intros ms' (m1 & -> & H1 & TS1 & IR1' & ZS1 & BY1). clear IR ZS BY. rename H into H0. rename H1 into H.
  pose proof (holds_slice m1 cp cmp cICONS1 (clen - 2) BY1 ltac:(lia) ltac:(lia) ltac:(lia)) as HLD.
  eapply implM_evt with (P := fun ms' => exists m' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      OF.frame_mod m1 m' [(Z_to_bv 64 (usp + -192 - 96), 96); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 p, 7176)] /\   (* 1.4: inflateSync's 64-byte frame and the 32 inflateReset pushes below it *)
      0 <= ZI.zr_consumed cIR2 <= clen - 2 /\
      fl_irep CT1 m' (IP (usp + -192) p 0) cIS2 /\
      izs_cells (fl_msga CT1) m' (usp + -192) (cp + cICONS1 + ZI.zr_consumed cIR2) (ZI.zlength (ZI.zc_input cIZC2) - ZI.zr_consumed cIR2)
                (up + cINOUT1) (n - cINOUT1) (ZI.zr_strm cIR2) p FL_ZCALLOC FL_ZCFREE /\ ZIS.is_window_blk cIS2 = None /\
      ms' = MS (mkR y1 (Z_to_bv 64 (usp + -192)) gp tp y5 y6 y7 (Z_to_bv 64 (clen - 2)) (Z_to_bv 64 n) (Z_to_bv 64 (ZI.zr_rc cIR2)) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F1 (Z_to_bv 64 0x161dc) fc1 None m' (seg_rom psegs)).
  { eapply (isy_evt FLIB F1 fc1 _ m1 (usp + -192) p 0 (usp + -192) 0x161dc (cp + cICONS1) (up + cINOUT1) ATOP cIS1 cIZC2).
    - split; [lia| reflexivity].
    - apply t_mod16.
    - lia.
    - lia.
    - lia.
    - unfold OL.blocks_ok, OL.iblocks. cbn [OL.ip_p OL.ip_w Z.eqb app]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      exact (blk_okz_of_MID _ _ _ _ pp p 7176 H ltac:(left; reflexivity)).
    - exact (MID_ro _ _ _ _ H).
    - lia.
    - lia.
    - apply t_mod8.
    - lia.
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - rewrite LEN2. cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.iblocks OL.ip_p OL.ip_w Z.eqb app]. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_ISTATE_N. repeat split; lia.
    - rewrite LEN2. intros a k Hin. cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
    - rewrite LEN2. lia.
    - rewrite LEN2. lia.
    - exact IR1'.
    - exact HLD.
    - rewrite LEN2. exact ZS1.
    - exact (lk_ssf _ _ _ _ LNK1 RC1).
    - intros m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 FM OUT0 CONS IR' ZS' WIN'.
      exists m', y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      split.
      { unfold OL.iblocks, OL.wz in FM. cbn [OL.ip_p OL.ip_w OL.ip_strm map fst snd app Z.eqb] in FM. exact FM. }
      split; [rewrite LEN2 in CONS; exact CONS|]. split; [exact IR'|]. split; [| split; [apply (proj1 WIN'); reflexivity| reflexivity]].
      replace (n - cINOUT1) with (ZI.zc_avail_out cIZC2) by reflexivity. exact ZS'. }
  intros ms' (m' & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FM & CONS & IR' & ZS' & WIN2 & ->).
  assert (FPOK : Forall (fp_ok [(pp, p, 7176); (pu, up, n); (pc, cp, cl0)])
             (fm_ivs [(Z_to_bv 64 (usp + -192 - 96), 96); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 p, 7176)])).
  { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; exists (pp, p, 7176); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_nil. }
  pose proof (MID_fm _ _ s m1 m' _ H FM FPOK) as H'.
  pose proof (same_on_frame_mod _ _ _ FM) as SO.
  assert (TS' : rw_cells psegs m' (usp + -80) (TSSV up cp n)).
  { eapply rw_cells_magree; [exact SO| exact TS1|]. intros a Ha. cbn in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
  assert (BY' : bytes_at psegs m' cp (map (Z_to_bv 8) cmp)).
  { eapply bytes_at_magree; [exact SO| exact BY1|]. intros a Ha. rewrite length_map in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
  rewrite (lk_is _ _ _ _ LNK1). rewrite LEN2 in ZS'.
  destruct (Z.eqb_spec (ZI.zr_rc cIR2) 0) as [RC0|RCNZ].
  -
    rewrite RC0.
    apply (L_inf3 s m' pp pc pu p cp up); [exact H'| exact TS'| exact CU1| change cICONS2 with (ZI.zr_consumed cIR2); lia| exact CU3| exact IR'| exact WIN2| | exact BY'| exact RC1| exact RC0].
    change cICONS2 with (ZI.zr_consumed cIR2). replace (cp + (cICONS1 + ZI.zr_consumed cIR2)) with (cp + cICONS1 + ZI.zr_consumed cIR2) by lia. exact ZS'.
  -
    assert (ER : In (ZI.zr_rc cIR2) SYNC_ERRS).
    { apply (fm_is_errs FLM cmp clen n). rewrite (lk_is _ _ _ _ LNK1). rewrite (proj2 (Z.eqb_neq _ _) RCNZ). reflexivity. }
    apply SYNC_ERRS_range in ER.
    eapply implM_evt with (P := fun ms' => ms' = _);
      [eapply (fl_seg_iE2 usp ltac:(lia)); [lia| exact RCNZ| exact (md_mi _ _ _ _ H')| apply relro_of_hc; exact (md_hc _ _ _ _ H')| reflexivity]| intros ms' ->].
    apply (L_idiag [(pp, p, FL_ISTATE_N)] clen s m' pc pu cp up (ZI.zr_rc cIR2) 0x103f9 HarnessC.MSG_INFLATESYNC);
      [eapply MID_perm; [exact H'| apply Permutation.Permutation_rev]| apply leak_ok_p| lia| cbn; auto| exact TS'].
Qed.

Lemma L_inf1 : forall s m (pp pc pu : bptr) (p cp up : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m ->
  rw_cells psegs m (usp + -80) (TSSV up cp n) ->
  fl_irep CT1 m (IP (usp + -192) p 0) (fl_is0 CT1) ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192) cp -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (usp + -192 + 8) 2 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 16) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 40) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 48) 0 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 56) p -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 64) FL_ZCALLOC -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 72) FL_ZCFREE ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 80) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -192 + 96) 1 ->
  bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  implM psegs (match fm_i1 FLM cmp n with
               | I1_E e => HarnessC.diag_zerr HarnessC.MSG_INFLATE e
               | I1_OK => match fm_is FLM cmp clen n with
                          | IS_E e => HarnessC.diag_zerr HarnessC.MSG_INFLATESYNC e
                          | IS_OK => match fm_i2 FLM cmp clen n with
                                     | I2_R rc3 => HarnessC.finish_sync raw_free pp None rc3
                                     | I2_W => wd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.WIN_N ;; HarnessC.finish_sync raw_free pp (Some wd) (fm_i2b FLM cmp clen n)
                                     end
                          end
               end ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 clen) (Z_to_bv 64 n) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x161b0) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pp pc pu p cp up x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TS IR C0 C8 C16 C40 C48 C56 C64 C72 C80 C96 BY.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof clen_range as CLN. pose proof cmp_len as CML. assert (ZN : ZI.zlength payload = n) by reflexivity. pose proof atop_range as AR. pose proof (md_clx _ _ _ _ H) as CLX.
  pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 2 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5. unfold FL_ISTATE_N in P3, P4, P5.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP. cbn [rev map app blk_addr blk_size fst snd] in AP.
  unfold FL_ISTATE_N in AP. destruct AP as (_ & (AK1 & AK2 & _) & (AQ1 & _) & _). unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in AK1, AK2, AQ1.
  pose proof (slice_length cmp 0 2 ltac:(lia) ltac:(lia) ltac:(lia)) as LEN1. cbn [Z.to_nat skipn] in LEN1.
  eapply implM_evt with (P := fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 0x161c8) (Z_to_bv 64 (usp + -192)) gp tp x5 x6 x7 (Z_to_bv 64 clen) (Z_to_bv 64 n) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 0)
                     x12 x13 x14 x15 x16 x17 (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F1 (Z_to_bv 64 0x1eee4) fc1 None m1 (seg_rom psegs)
      /\ MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m1 /\ rw_cells psegs m1 (usp + -80) (TSSV up cp n)
      /\ fl_irep CT1 m1 (IP (usp + -192) p 0) (fl_is0 CT1)
      /\ izs_cells (fl_msga CT1) m1 (usp + -192) cp 2 up n IZS0 p FL_ZCALLOC FL_ZCFREE
      /\ bytes_at psegs m1 cp (map (Z_to_bv 8) cmp)).
  { eapply (fl_seg_i1 usp _ n up clen lo m F1 fc1); [lia| lia| exact NR| lia| lia| apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)|].
    intros M1 MU WM MI1 ST1 RNO RAO. exists M1. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    split; [eapply (MID_munch _ _ s m M1 _ H MU WM MI1); apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]|].
    split; [eapply rw_cells_magree; [exact SO| exact TS|]; intros a Ha; cbn in Ha; cbn; lia|].
    split; [apply (irep_munch _ m M1 p (fl_is0 CT1) IR MU WM); intros x Hx; cbn; lia|].
    split.
    - unfold izs_cells. cbn [ZI.zs_total_in ZI.zs_total_out ZI.zs_msg ZI.zs_adler IZS0]. rewrite (fl_msga_null CT1).
      split; [eapply (cell8_same_on _ m M1); [exact SO| intros x Hx; cbn; lia| lia| lia| exact C0]|].
      split; [eapply (cell4_same_on _ m M1); [exact SO| intros x Hx; cbn; lia| lia| lia| exact C8]|].
      split; [eapply (cell8_same_on _ m M1); [exact SO| intros x Hx; cbn; lia| lia| lia| exact C16]|].
      split; [unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8; replace (usp + -192 + 24) with (usp + -168) by lia; exact RNO|].
      split; [unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4; replace (usp + -192 + 32) with (usp + -160) by lia; exact RAO|].
      repeat split.
      all: eapply (cell8_same_on _ m M1); [exact SO| | | | eassumption]; [intros x Hx; cbn; lia| lia| lia].
    - eapply bytes_at_magree; [exact SO| exact BY|]. intros a Ha. rewrite length_map in Ha. cbn. lia. }
  intros ms' (m1 & -> & H1 & TS1 & IR1 & ZS1 & BY1). clear IR BY C0 C8 C16 C40 C48 C56 C64 C72 C80 C96. rename H into H0. rename H1 into H.
  pose proof (holds_slice m1 cp cmp 0 2 BY1 ltac:(lia) ltac:(lia) ltac:(lia)) as HLD. cbn [Z.to_nat skipn] in HLD. rewrite Z.add_0_r in HLD.
  eapply implM_evt with (P := fun ms' => exists m' (nout : Z) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      OF.frame_mod m1 m' [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 up, nout); (Z_to_bv 64 p, 7176)] /\
      0 <= nout <= n /\
      (~ InflateRc.RR (ZI.zr_rc cIR1) -> nout = cINOUT1 /\ 0 <= cICONS1 <= 2 /\
         fl_irep CT1 m' (IP (usp + -192) p 0) cIS1 /\
         izs_cells (fl_msga CT1) m' (usp + -192) (cp + cICONS1) (2 - cICONS1) (up + nout) (n - nout) (ZI.zr_strm cIR1) p FL_ZCALLOC FL_ZCFREE /\
         ZIS.is_window_blk cIS1 = None) /\
      ms' = MS (mkR y1 (Z_to_bv 64 (usp + -192)) gp tp y5 y6 y7 (Z_to_bv 64 clen) (Z_to_bv 64 n) (Z_to_bv 64 (ZI.zr_rc cIR1)) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F1 (Z_to_bv 64 0x161c8) fc1 None m' (seg_rom psegs)).
  { eapply (inf_evt FLIB F1 fc1 _ m1 (usp + -192) p 0 (usp + -192) 0x161c8 cp up ATOP 0 (fl_is0 CT1) cIZC1 (WANS WB)).
    - split; [lia| reflexivity].
    - apply t_mod16.
    - lia.
    - lia.
    - lia.
    - unfold OL.blocks_ok, OL.iblocks. cbn [OL.ip_p OL.ip_w Z.eqb app]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      exact (blk_okz_of_MID _ _ _ _ pp p 7176 H ltac:(left; reflexivity)).
    - exact (MID_ro _ _ _ _ H).
    - lia.
    - lia.
    - apply t_mod8.
    - lia.
    - lia.
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - cbn [ZI.zc_avail_out cIZC1 IZC1].
      pose proof (wr_at_store_ok psegs m1 up n 0 (Z.to_nat n) (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) (pu, up, n) ltac:(right; left; reflexivity)) ltac:(lia) ltac:(lia)) as X.
      rewrite Z.add_0_r in X. exact X.
    - rewrite LEN1. cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.iblocks OL.ip_p OL.ip_w Z.eqb ZI.zc_avail_out cIZC1 IZC1 app]. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_ISTATE_N.
      change (ZI.zlength payload) with n. repeat split; lia.
    - rewrite LEN1. cbn [ZI.zc_avail_out cIZC1 IZC1]. change (ZI.zlength payload) with n. intros a k Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
    - rewrite LEN1. lia.
    - cbn [ZI.zc_avail_out cIZC1 IZC1]. change (ZI.zlength payload) with n. lia.
    - cbn [ZI.zc_avail_out cIZC1 IZC1]. change (ZI.zlength payload) with n. lia.
    - rewrite LEN1. lia.
    - exact IR1.
    - split; [intros _; exact (fl_is0_nowin CT1)| intros _; reflexivity].
    - exact HLD.
    - rewrite LEN1. exact ZS1.
    - exact (lk_isf1 _ _ _ _ LNK1).
    - intros m' nout y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 _ NO FM GRD.
      exists m', nout, y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      cbn [ZI.zc_avail_out cIZC1 IZC1] in NO. change (ZI.zlength payload) with n in NO.
      split.
      { unfold OL.iblocks, OL.wz in FM. cbn [OL.ip_p OL.ip_w OL.ip_strm map fst snd app Z.eqb] in FM.
        replace (usp + -192 - FL_IFR) with (usp + -192 - 464) in FM by reflexivity. exact FM. }
      split; [exact NO|]. split; [| reflexivity]. intros NRR. destruct (GRD NRR) as (NO' & CONS & IR' & ZS' & HLD' & WIN').
      rewrite LEN1 in CONS, ZS'. cbn [ZI.zc_avail_out cIZC1 IZC1] in ZS'. change (ZI.zlength payload) with n in ZS'.
      split; [exact NO'|]. split; [exact CONS|]. split; [exact IR'|]. split; [exact ZS'| apply (proj1 WIN'); reflexivity].
    - intros m' nout y1 y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ASK'.
      exfalso. pose proof (lk_nw1 _ _ _ _ LNK1) as NW. change (snd cICALL1) with (snd (ZHF.inflate_p ZIS.ivar_ref (WANS WB) (fl_is0 CT1) cIZC1 0)) in NW.
      rewrite NW in ASK'. discriminate. }
  intros ms' (m' & nout & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FM & NO & GRD & ->).
  assert (FPOK : Forall (fp_ok [(pp, p, 7176); (pu, up, n); (pc, cp, cl0)])
             (fm_ivs [(Z_to_bv 64 (usp + -192 - 464), 464); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 up, nout); (Z_to_bv 64 p, 7176)])).
  { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; exists (pu, up, n); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pp, p, 7176); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_nil. }
  pose proof (MID_fm _ _ s m1 m' _ H FM FPOK) as H'.
  pose proof (same_on_frame_mod _ _ _ FM) as SO.
  assert (TS' : rw_cells psegs m' (usp + -80) (TSSV up cp n)).
  { eapply rw_cells_magree; [exact SO| exact TS1|]. intros a Ha. cbn in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
  assert (BY' : bytes_at psegs m' cp (map (Z_to_bv 8) cmp)).
  { eapply bytes_at_magree; [exact SO| exact BY1|]. intros a Ha. rewrite length_map in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
  rewrite (lk_i1 _ _ _ _ LNK1).
  destruct (Z.eqb_spec (ZI.zr_rc cIR1) 0) as [RC0|RCNZ].
  -
    destruct (GRD ltac:(rewrite RC0; unfold InflateRc.RR, ZI.Z_NEED_DICT, ZI.Z_MEM_ERROR, ZI.Z_STREAM_ERROR; lia)) as (NOE & CONS & IR' & ZS' & WIN1). subst nout.
    rewrite RC0. apply (L_isy s m' pp pc pu p cp up); [exact H'| exact TS'| exact CONS| exact NO| exact IR'| exact WIN1| exact ZS'| exact BY'| exact RC0].
  -
    assert (ER : In (ZI.zr_rc cIR1) INFL_ERRS).
    { apply (fm_i1_errs FLM cmp n). rewrite (lk_i1 _ _ _ _ LNK1). rewrite (proj2 (Z.eqb_neq _ _) RCNZ). reflexivity. }
    apply INFL_ERRS_range in ER.
    eapply implM_evt with (P := fun ms' => ms' = _);
      [eapply (fl_seg_iE1 usp ltac:(lia)); [lia| exact RCNZ| exact (md_mi _ _ _ _ H')| apply relro_of_hc; exact (md_hc _ _ _ _ H')| reflexivity]| intros ms' ->].
    apply (L_idiag [(pp, p, FL_ISTATE_N)] clen s m' pc pu cp up (ZI.zr_rc cIR1) 0x10570 HarnessC.MSG_INFLATE);
      [eapply MID_perm; [exact H'| apply Permutation.Permutation_rev]| apply leak_ok_p| lia| cbn; auto| exact TS'].
Qed.

Lemma L_ii : forall s m (pp pc pu : bptr) (p cp up : Z) (p12 p56 p88 : list byte)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pp, p, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s m ->
  rw_cells psegs m (usp + -192) (TSC p12 p56 p88 up cp n) -> rw_cells psegs m (usp + -224) (IIC up n clen) ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m p FL_ISTATE_N ->
  bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  implM psegs (match fm_i1 FLM cmp n with
               | I1_E e => HarnessC.diag_zerr HarnessC.MSG_INFLATE e
               | I1_OK => match fm_is FLM cmp clen n with
                          | IS_E e => HarnessC.diag_zerr HarnessC.MSG_INFLATESYNC e
                          | IS_OK => match fm_i2 FLM cmp clen n with
                                     | I2_R rc3 => HarnessC.finish_sync raw_free pp None rc3
                                     | I2_W => wd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.WIN_N ;; HarnessC.finish_sync raw_free pp (Some wd) (fm_i2b FLM cmp clen n)
                                     end
                          end
               end ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -224)) gp tp x5 x6 x7 (Z_to_bv 64 clen) (Z_to_bv 64 7176) (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (usp + -192)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 FL_A_II) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pp pc pu p cp up p12 p56 p88 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TSCc IICc ZP BY.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof clen_range as CLN. pose proof cmp_len as CML. assert (ZN : ZI.zlength payload = n) by reflexivity. pose proof atop_range as AR. pose proof (md_clx _ _ _ _ H) as CLX.
  pose proof (MID_blk _ _ _ _ (pp, p, FL_ISTATE_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 2 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5. unfold FL_ISTATE_N in P3, P4, P5.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP. cbn [rev map app blk_addr blk_size fst snd] in AP.
  unfold FL_ISTATE_N in AP. destruct AP as (_ & (AK1 & AK2 & _) & (AQ1 & _) & _). unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in AK1, AK2, AQ1.
  unfold TSC in TSCc. unfold IIC in IICc.
  change ([C8 (Z_to_bv 64 cp); C4 (Z_to_bv 64 2); CB 36 p12; C8 (Z_to_bv 64 0); CB 8 p56;
           C8 (Z_to_bv 64 0x1a9f4); C8 (Z_to_bv 64 0x1aa04); C8 (Z_to_bv 64 0); CB 24 p88;
           C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 up); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x16370)])
    with ([C8 (Z_to_bv 64 cp); C4 (Z_to_bv 64 2); CB 36 p12; C8 (Z_to_bv 64 0); CB 8 p56;
           C8 (Z_to_bv 64 0x1a9f4); C8 (Z_to_bv 64 0x1aa04); C8 (Z_to_bv 64 0); CB 24 p88] ++ TSSV up cp n) in TSCc.
  pose proof (rw_cells_app_split m _ _ _ TSCc) as [TS1 TS]. change (Z.of_nat (cells_size _)) with 112 in TS.
  replace (usp + -192 + 112) with (usp + -80) in TS by lia.
  eapply implM_evt with (P := fun ms' => exists m' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      OF.frame_mod m m' [(Z_to_bv 64 (usp + -192 - 1024), 1024); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 p, 7176)] /\
      OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 16) 0 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 40) 0 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 48) 0 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 56) p /\
      OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 64) FL_ZCALLOC /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 72) FL_ZCFREE /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 80) 0 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192 + 96) 1 /\
      OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (usp + -192) cp /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m' (usp + -192 + 8) 2 /\
      fl_irep CT1 m' (IP (usp + -192) p 0) (fl_is0 CT1) /\
      ms' = MS (mkR y1 (Z_to_bv 64 (usp + -192)) gp tp y5 y6 y7 (Z_to_bv 64 clen) (Z_to_bv 64 n) (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 up) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F1 (Z_to_bv 64 0x161b0) fc1 None m' (seg_rom psegs)).
  replace (Z_to_bv 64 (usp + -224)) with (Z_to_bv 64 (usp + -192 - 32)) by (f_equal; lia).
  { eapply (ii_evt FLIB F1 fc1 _ m (usp + -192) p (usp + -192) ATOP 0x161b0 clen n up cp 2).
    - apply t_mod16.
    - lia.
    - lia.
    - lia.
    - unfold OL.blocks_ok, OL.iblocks. cbn [OL.ip_p OL.ip_w Z.eqb app]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      exact (blk_okz_of_MID _ _ _ _ pp p 7176 H ltac:(left; reflexivity)).
    - exact (MID_ro _ _ _ _ H).
    - lia.
    - apply t_mod8.
    - lia.
    - apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all]. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart. repeat split; lia.
    - right. lia.
    - split; [lia| reflexivity].
    - lia.
    - lia.
    - lia.
    - exact ZP.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact IICc 24%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact IICc 16%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact IICc 8%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact IICc 0%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact TS1 48%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, FL_ZCALLOC. cell_fact TS1 64%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, FL_ZCFREE. cell_fact TS1 72%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact TS1 80%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. replace (usp + -192) with (usp + -192 + 0) by lia. cell_fact TS1 0%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact TS1 8%nat.
    - intros m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 FM E1 E2 E3 E4 E5 E6 E7 E8 IR G0 G8.
      exists m', y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      replace (usp + -192 - FL_FRA) with (usp + -192 - 1024) in FM by reflexivity.
      repeat (split; [assumption|]). reflexivity. }
  intros ms' (m' & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FM & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & G0 & G8 & IR & ->).
  assert (FPOK : Forall (fp_ok [(pp, p, 7176); (pu, up, n); (pc, cp, cl0)])
             (fm_ivs [(Z_to_bv 64 (usp + -192 - 1024), 1024); (Z_to_bv 64 (usp + -192), 112); (Z_to_bv 64 p, 7176)])).
  { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; exists (pp, p, 7176); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_nil. }
  pose proof (MID_fm _ _ s m m' _ H FM FPOK) as H'.
  pose proof (same_on_frame_mod _ _ _ FM) as SO.
  assert (TS' : rw_cells psegs m' (usp + -80) (TSSV up cp n)).
  { eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. cbn in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
  assert (BY' : bytes_at psegs m' cp (map (Z_to_bv 8) cmp)).
  { eapply bytes_at_magree; [exact SO| exact BY|]. intros a Ha. rewrite length_map in Ha. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. lia. }
  apply (L_inf1 s m' pp pc pu p cp up); [exact H'| exact TS'| exact IR| exact G0| exact G8| exact E1| exact E2| exact E3| exact E4| exact E5| exact E6| exact E7| exact E8| exact BY'].
Qed.

Lemma L_ts1 : forall s m (pc pu : bptr) (cp up : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pu, up, n); (pc, cp, cl0)] clen s m ->
  bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  implM psegs (HarnessC.test_sync_m FLM raw_malloc raw_free fresh_topb cmp clen n ;;; REST pc pu) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 up) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 cp) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x1635c) fc1 None m (seg_rom psegs)).
Proof.
  intros s m pc pu cp up x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H BY.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof clen_range as CLN. pose proof cmp_len as CML. assert (ZN : ZI.zlength payload = n) by reflexivity. pose proof atop_range as AR. pose proof (md_clx _ _ _ _ H) as CLX.
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5.
  destruct (md_hf _ _ _ _ H) as [pad HFc].
  unfold HarnessC.test_sync_m, HarnessC.ISTATE_N. apply implM_bind_assoc.
  eapply implM_evt with (P := fun ms' => exists m1 (p12 p56 p88 : list byte) (y14 : word),
      ms' = MS (mkR (Z_to_bv 64 0x1edec) (Z_to_bv 64 (usp + -224)) gp tp x5 x6 x7 (Z_to_bv 64 clen) (Z_to_bv 64 7176) (Z_to_bv 64 7176) (Z_to_bv 64 1) (Z_to_bv 64 7176)
                     (Z_to_bv 64 0x1a9f4) y14 x15 x16 x17 (Z_to_bv 64 (usp + -192)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F1 (Z_to_bv 64 0x23abc) fc1 None m1 (seg_rom psegs)
      /\ MID [(pu, up, n); (pc, cp, cl0)] clen s m1 /\ stk psegs m1 lo (usp + -224)
      /\ rw_cells psegs m1 (usp + -192) (TSC p12 p56 p88 up cp n) /\ rw_cells psegs m1 (usp + -224) (IIC up n clen)
      /\ bytes_at psegs m1 cp (map (Z_to_bv 8) cmp)).
  { eapply (fl_seg_ts1 usp ltac:(lia) SP16 _ n cp up clen lo pad m F1 fc1);
      [lia| lia| exact NR| lia| lia| lia| apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)| apply relro_of_hc; exact (md_hc _ _ _ _ H)| exact HFc|].
    intros M1 p12 p56 p88 y14 MU WM MI1 ST1 TSCc IICc HF1. exists M1, p12, p56, p88, y14. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    split; [eapply (MID_munch _ _ s m M1 _ H MU WM MI1); apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]|].
    split; [exact ST1|]. split; [exact TSCc|]. split; [exact IICc|].
    eapply bytes_at_magree; [exact SO| exact BY|]. intros a Ha. rewrite length_map in Ha. cbn. lia. }
  intros ms' (m1 & p12 & p56 & p88 & y14 & -> & H1 & ST1 & TSCc & IICc & BY1). clear BY HFc. rename H into H0. rename H1 into H.
  destruct (md_err _ _ _ _ H) as [errv ER].
  eapply implM_zreq.
  { unfold rmalloc_stmt_z in MALLOCZ.
    eapply MALLOCZ with (lo := lo) (B := AB) (LB := [(pu, up, n); (pc, cp, cl0)] ++ LB) (n := 7176) (errv := errv);
      rewrite ?(unsigned_lit (usp + -224)) by lia.
    - exact (md_heap _ _ _ _ H).
    - exact (md_aux _ _ _ _ H).
    - lia.
    - exact ST1.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros pp s' ms' PO FRSH.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -224)) in ST' by lia. rewrite ?(unsigned_lit (usp + -224)) in HPR by lia.
  destruct RES as (A & junk & -> & BR & HEAP' & BLK & _ & ZJ). specialize (ZJ FRSH). subst junk.
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ 7176 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(pp, A, FL_ISTATE_N); (pu, up, n); (pc, cp, cl0)] clen s' m').
  { apply (MID_heap _ _ _ clen s s' m1 m' (usp + -224) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO'.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  apply (L_ii s' m' pp pc pu A cp up p12 p56 p88); [exact H'| | | apply (zeros_at_of_chunk m' A 7176 BLK); lia|].
  - eapply rw_cells_magree; [exact SO'| exact TSCc|]. intros a Ha. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact SO'| exact IICc|]. intros a Ha. left. cbn in Ha. lia.
  - eapply bytes_at_magree; [exact SO'| exact BY1|]. intros a Ha. rewrite length_map in Ha. right; right. exists (pc, cp, cl0).
    split; [apply in_or_app; left; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
Qed.

End INFL.

Let LNK0 : fl_links CT FLM WB payload := LNK (OP.mkFP F fc).
Definition KTS (pc pu : bptr) : Z -> M PState Z :=
  fun clen' => HarnessC.test_sync_m FLM raw_malloc raw_free fresh_topb cmp clen' n ;;; REST pc pu.
Definition TFT : M PState Z :=
  if fm_busy FLM payload then HarnessC.diag_zerr HarnessC.MSG_DEFLATEEND ZE_DATA_ERROR ;;; mret cl0 else mret (fm_tot FLM payload).
Definition DEC (m : mem) (sa cp : Z) : Prop :=
  OP.rdn psegs m (Z_to_bv 64 (usp + -144)) 8 = Some (Z_to_le_bytes 8 sa) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 FL_ZCFREE) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -216)) 8 = Some (Z_to_le_bytes 8 0x160a0) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -224)) 8 = Some (Z_to_le_bytes 8 (usp + -40)) /\
  OP.rdn psegs m (Z_to_bv 64 (usp + -232)) 8 = Some (Z_to_le_bytes 8 cp).

Lemma DEC_heap : forall LBp SPc m m' sa cp, rheap_pres LBp SPc m m' -> SPc <= usp + -240 -> DEC m sa cp -> DEC m' sa cp.
Proof.
  intros LBp SPc m m' sa cp HPR HS (E1 & E2 & E3 & E4 & E5 & E6). pose proof usp_facts as (U1 & U2 & U3 & U4). unfold DEC.
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  repeat split; (eapply (rdn_same_on8 _ m m' _ _ _ SO); [| | | eassumption]; [intros x Hx; left; cbn in Hx; lia| lia| cbn; lia]).
Qed.
Lemma scell_heap : forall LBp SPc m m' (ps : bptr) sa off bs k, rheap_pres LBp SPc m m' -> In (ps, sa, FL_DSTATE_N) LBp ->
  0 <= off -> off + Z.of_nat k <= FL_DSTATE_N -> 0 <= sa -> sa + FL_DSTATE_N < 2^64 ->
  OP.rdn psegs m (Z_to_bv 64 (sa + off)) k = Some bs -> OP.rdn psegs m' (Z_to_bv 64 (sa + off)) k = Some bs.
Proof.
  intros LBp SPc m m' ps sa off bs k HPR Is Ho Hoff Hs Hs2 C. unfold FL_DSTATE_N in *.
  eapply (rdn_same_on8 _ m m' (sa + off) k bs (same_on_rheap_pres _ _ _ _ HPR)); [| lia| lia| exact C].
  intros x Hx. right; right. exists (ps, sa, 5968). split; [exact Is| cbn [blk_addr blk_size fst snd]; lia].
Qed.

Lemma MID_clx : forall LBx clx clx' s m m' pad,
  MID LBx clx s m -> munch [(usp + -40, usp + -32)] m m' -> wmono psegs m m' -> mem_inv psegs m' ->
  rw_cells psegs m' (usp - 48) (HF pad clx') -> 0 <= clx' < 2^63 -> MID LBx clx' s m'.
Proof.
  intros LBx clx clx' s m m' pad H MU WM MI' HFc CLX'.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof atop_range as AR.
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  assert (BLK : forall b, In b (LBx ++ LB) -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (MID_blk _ _ _ _ b H Hb)).
  assert (OUT : forall x, (x < usp - 40 \/ usp - 32 <= x) -> outside [(usp + -40, usp + -32)] x) by (intros x Hx; cbn; lia).
  constructor.
  - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact (md_heap _ _ _ _ H)| exact MU| exact WM|].
    apply Forall_cons; [left; cbn [fst]; lia| apply Forall_nil].
  - exact MI'.
  - eapply stk_wmono; [exact (md_stk _ _ _ _ H)| lia| exact WM].
  - destruct (md_err _ _ _ _ H) as [errv ER]. exists errv. eapply rw_cells_magree; [exact SO| exact ER|].
    intros a Ha. apply OUT. rewrite TP in Ha. unfold wz, RATP in Ha. rewrite unsigned_lit in Ha by lia.
    change (Z.of_nat (cells_size [C4 errv])) with 4 in Ha. unfold RERRNO in Ha. lia.
  - eapply rauxv_ok_frame; [exact (md_aux _ _ _ _ H)| exact MU| exact WM|].
    apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; split; [lia| right; lia]| apply Forall_nil].
  - eapply harness_pres_trans; [exact (md_pres _ _ _ _ H)|]. intros a Ha Hc NB. apply SO; [exact Ha|]. apply OUT.
    destruct Hc as [Hc|[[Hc NS]|(b & Hb & Hr)]]; [right; lia| left; lia|].
    pose proof (BLK b ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & B4 & _). left. lia.
  - exact (md_so _ _ _ _ H).
  - intros a Ha. destruct (SO a ltac:(unfold PRELRO_LO, PRELRO_HI in Ha; lia) ltac:(apply OUT; unfold PRELRO_LO, PRELRO_HI in *; lia)) as [E _].
    unfold wa in E. rewrite E. exact (md_hc _ _ _ _ H a Ha).
  - destruct (md_sf _ _ _ _ H) as (flags & mode & e & wend & tail & FC & FL & WE & HE). exists flags, mode, e, wend, tail.
    split; [| split; [exact FL| split; [exact WE| exact HE]]].
    eapply rw_cells_magree; [exact SO| exact FC|]. intros a Ha. rewrite file_cells_size in Ha. apply OUT. lia.
  - exists pad. exact HFc.
  - exact CLX'.
  - eapply rw_cells_magree; [exact SO| exact (md_st _ _ _ _ H)|]. intros a Ha. apply OUT. cbn in Ha. unfold HDATA in *. lia.
  - eapply pay_same_on; [exact SO| | exact (md_pay _ _ _ _ H)]. intros b a Hb Ha. apply OUT.
    pose proof (BLK b ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & B4 & _). left. lia.
  - eapply pwr_same_on; [exact SO| | exact (md_pwr _ _ _ _ H)]. intros b a Hb Ha. apply OUT.
    pose proof (BLK b ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & B4 & _). left. lia.
  - eapply Forall_impl; [| exact (md_wr _ _ _ _ H)]. intros b (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|].
    intros i Hi. apply WM. apply W2. exact Hi.
Qed.

Lemma L_tf_ret : forall (F1 : bvmap 5 word) (fc1 : bv 32) s m (pc pu : bptr) (cp up : Z)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  frm0 fc1 -> MID [(pu, up, n); (pc, cp, cl0)] clen s m ->
  rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  implM psegs (KTS pc pu clen) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F1 (Z_to_bv 64 0x16140) fc1 None m (seg_rom psegs)).
Proof.
  intros F1 fc1 s m pc pu cp up x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 FRM1 H TS BY.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof cl_range as CLR. pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5.
  eapply implM_evt with (P := fun ms' => ms' = _);
    [eapply (fl_seg_tf_ret usp _ n cp up m F1 fc1); [lia| lia| lia| exact TS| exact (md_mi _ _ _ _ H)| reflexivity]| intros ms' ->].
  unfold KTS. apply (L_ts1 F1 fc1 FRM1 s m pc pu cp up); [exact H| exact BY].
Qed.

Lemma L_tf_ok : forall s m (pc pu : bptr) (cp up : Z)
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  MID [(pu, up, n); (pc, cp, cl0)] cl0 s m -> fm_busy FLM payload = false ->
  rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT) ->
  implM psegs (mbind TFT (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -40)) x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x160a0) fc None m (seg_rom psegs)).
Proof.
  intros s m pc pu cp up x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 H NB TS BY TOT.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  pose proof (lk_tot _ _ _ _ LNK0 NB) as ET. pose proof (fm_tot_range FLM payload) as TR.
  assert (ECL : clen = cDTOT). { unfold fm_clen. rewrite NB. exact ET. }
  assert (TR' : 0 <= cDTOT < 2^63). { rewrite <- ET. unfold zlength in CLR. lia. }
  destruct (md_hf _ _ _ _ H) as [pad HFc].
  unfold TFT. rewrite NB. apply implM_retb. rewrite ET, <- ECL.
  eapply implM_evt with (P := fun ms' => exists m1, ms' = _ /\ MID [(pu, up, n); (pc, cp, cl0)] clen s m1 /\
      rw_cells psegs m1 (usp + -88) (TSV s3 up cp n) /\ bytes_at psegs m1 cp (map (Z_to_bv 8) cmp)).
  { rewrite ECL. replace (usp - 48) with (usp + -48) in HFc by lia. rewrite <- cl_eq in HFc.
    eapply (fl_seg_tf_ok usp _ n cDTOT pad m F fc); [lia| exact HFc| exact (md_mi _ _ _ _ H)| exact TOT|].
    intros M1 MU WM MI1 HF1. exists M1. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    split; [apply (MID_clx _ cl0 cDTOT s m M1 pad H MU WM MI1); [replace (usp - 48) with (usp + -48) by lia; exact HF1| exact TR']|].
    split; [eapply rw_cells_magree; [exact SO| exact TS|]; intros a Ha; cbn in Ha; cbn; lia|].
    eapply bytes_at_magree; [exact SO| exact BY|]. intros a Ha. rewrite length_map in Ha. cbn.
    pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(right; left; reflexivity)) as (_ & _ & _ & K4 & _). cbn [blk_addr blk_size fst snd] in K4. lia. }
  intros ms' (m1 & -> & H1 & TS1 & BY1).
  apply (L_tf_ret F fc s m1 pc pu cp up); [exact FRM| exact H1| exact TS1| exact BY1].
Qed.

Lemma L_tf_dE : forall s m (pc pu : bptr) (cp up : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  MID [(pu, up, n); (pc, cp, cl0)] cl0 s m -> fm_busy FLM payload = true ->
  rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  implM psegs (mbind TFT (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (-3)) x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x160a0) fc None m (seg_rom psegs)).
Proof.
  intros s m pc pu cp up x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 H B TS BY.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  assert (ECL : clen = cl0). { unfold fm_clen. rewrite B. unfold zlength. reflexivity. }
  unfold TFT. rewrite B. apply implM_bind_assoc.
  eapply implM_evt with (P := fun ms' => ms' = _);
    [eapply (fl_seg_tf_dE usp); [exact (md_mi _ _ _ _ H)| apply relro_of_hc; exact (md_hc _ _ _ _ H)| reflexivity]| intros ms' ->].
  unfold HarnessC.diag_zerr, ZE_DATA_ERROR.
  eapply implM_bind.
  { pose proof (FPRINTF 0x1030b HarnessC.MSG_DEFLATEEND ltac:(cbn; auto)) as FPR. unfold fprintf_zerr_stmt_fl in FPR.
    eapply (FPR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s (-3) lo CAN FWX SWF);
      rewrite ?(unsigned_lit (usp + -208)) by lia.
    - apply stderr_wfile0_wfile. exact (md_sf _ _ _ _ H).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - apply mod32_of_wrap.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - unfold FPRINTF_DEPTH. lia.
    - unfold GLOBALS_TOP. lia.
    - lia.
    - exact (MID_ssp _ _ _ _ H).
    - exact (md_mi _ _ _ _ H).
    - exact FRM. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FK & ST' & SF' & SSP' & ->).
  rewrite ?(unsigned_lit (usp + -208)) in MU by lia.
  pose proof (MID_stdio _ _ s m m' (usp + -208) H MU WM MI' SF' ltac:(lia)) as H'.
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  apply implM_retb. rewrite <- ECL.
  apply (L_tf_ret Ft fc' s m' pc pu cp up); [exact FRM'| rewrite ECL; exact H'| |].
  - eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. cbn in Ha. cbn. lia.
  - eapply bytes_at_magree; [exact SO| exact BY|]. intros a Ha. rewrite length_map in Ha. cbn.
    pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(right; left; reflexivity)) as (_ & _ & _ & K4 & K5). cbn [blk_addr blk_size fst snd] in K4, K5. pose proof atop_range. lia.
Qed.

Lemma L_de_tail : forall s m (pc pu : bptr) (cp up st sa : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  MID [(pu, up, n); (pc, cp, cl0)] cl0 s m -> (st = 113 \/ st = 666) -> fm_busy FLM payload = (st =? 113) ->
  DEC m sa cp -> rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT) ->
  implM psegs (mbind TFT (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -240)) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16834) fc None m (seg_rom psegs)).
Proof.
  intros s m pc pu cp up st sa x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 H ST B DC TS BY TOT.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5.
  destruct DC as (E1 & E2 & E3 & E4 & E5 & E6).
  set (r := if st =? 113 then -3 else 0).
  eapply implM_evt with (P := fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 0x160a0) (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                     x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x160a0) fc None m1 (seg_rom psegs)
      /\ MID [(pu, up, n); (pc, cp, cl0)] cl0 s m1 /\ rw_cells psegs m1 (usp + -88) (TSV s3 up cp n) /\ bytes_at psegs m1 cp (map (Z_to_bv 8) cmp)
      /\ OP.rdn psegs m1 (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT)).
  { eapply (fl_seg_de_tail usp ltac:(lia) _ cp st r lo m F fc);
      [lia| lia| lia| subst r; destruct ST as [-> | ->]; [right| left]; split; reflexivity
      | apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)| exact E4| exact E5| exact E6|].
    intros M1 MU WM MI1 ST1 RZ. exists M1. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    split; [eapply (MID_munch _ _ s m M1 _ H MU WM MI1); apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]|].
    split; [eapply rw_cells_magree; [exact SO| exact TS|]; intros a Ha; cbn in Ha; cbn; lia|].
    split; [eapply bytes_at_magree; [exact SO| exact BY|]; intros a Ha; rewrite length_map in Ha; cbn; lia|].
    eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; cbn in Hx; cbn; lia| lia| cbn; lia| exact TOT]. }
  intros ms' (m1 & -> & H1 & TS1 & BY1 & TOT1). subst r.
  destruct (Z.eqb_spec st 113) as [E113|N113].
  - apply (L_tf_dE s m1 pc pu cp up); [exact H1| exact B| exact TS1| exact BY1].
  - apply (L_tf_ok s m1 pc pu cp up); [exact H1| exact B| exact TS1| exact BY1| exact TOT1].
Qed.

Lemma tflush_heap : forall LBp m m' (pc pu : bptr) cp up,
  rheap_pres LBp (usp + -240) m m' -> In (pc, cp, cl0) LBp -> 0 <= cp -> cp + cl0 < 2^64 ->
  (rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> rw_cells psegs m' (usp + -88) (TSV s3 up cp n)) /\
  (bytes_at psegs m cp (map (Z_to_bv 8) cmp) -> bytes_at psegs m' cp (map (Z_to_bv 8) cmp)) /\
  (forall v, OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some v -> OP.rdn psegs m' (Z_to_bv 64 (usp + -160)) 8 = Some v).
Proof.
  intros LBp m m' pc pu cp up HPR Ic Hc Hc2. pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof cmp_len as CML.
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  split; [| split].
  - intros TS. eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. left. cbn in Ha. lia.
  - intros BY. eapply bytes_at_magree; [exact SO| exact BY|]. intros a Ha. rewrite length_map in Ha. right; right. exists (pc, cp, cl0).
    split; [exact Ic| cbn [blk_addr blk_size fst snd]; lia].
  - intros v TOT. eapply (rdn_same_on8 _ m m' _ _ _ SO); [intros x Hx; left; cbn in Hx; lia| lia| cbn; lia| exact TOT].
Qed.

Lemma L_de5 : forall s m (ps pc pu : bptr) (sa cp up st : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  MID [(ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m -> (st = 113 \/ st = 666) -> fm_busy FLM payload = (st =? 113) ->
  DEC m sa cp -> rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT) ->
  implM psegs (mbind (raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -240)) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16818) fc None m (seg_rom psegs)).
Proof.
  intros s m ps pc pu sa cp up st x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 H ST B DC TS BY TOT.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  destruct (md_err _ _ _ _ H) as [errv ER].
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(left; reflexivity)) as (S1 & S2 & S3 & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 2 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in S1, S2, S3, S4, S5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5. unfold FL_DSTATE_N in *.
  pose proof DC as (E1 & E2 & E3 & E4 & E5 & E6).
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply (fl_de5 usp _ m F fc sa); [lia| exact E1| exact E2| exact E3| reflexivity]| intros ms' ->].
  apply implM_bind_assoc.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (ps, sa, 5968) :: ([(pu, up, n); (pc, cp, cl0)] ++ LB)) (p := ps) (A := sa) (n := 5968) (errv := errv);
      rewrite ?(unsigned_lit (usp + -240)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -240)) in ST' by lia. rewrite ?(unsigned_lit (usp + -240)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove ps ((ps, sa, 5968) :: ([(pu, up, n); (pc, cp, cl0)] ++ LB))) with ([(pu, up, n); (pc, cp, cl0)] ++ LB) in HPR, HEAP' by (symmetry; apply (RDriver_facts.lb_remove_head (ps, sa, 5968)); exact ND).
  assert (H' : MID [(pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ [(pu, up, n); (pc, cp, cl0)] _ cl0 s s' m m' (usp + -240) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  destruct (tflush_heap _ m m' pc pu cp up HPR ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as (TSh & BYh & TOTh).
  apply (L_de_tail s' m' pc pu cp up st sa); [exact H'| exact ST| exact B| exact (DEC_heap _ _ m m' sa cp HPR ltac:(lia) DC)| exact (TSh TS)| exact (BYh BY)| exact (TOTh _ TOT)].
Qed.

Definition SPTR (m : mem) (sa wnd prv hd : Z) : Prop :=
  OP.rdn psegs m (Z_to_bv 64 (sa + 96)) 8 = Some (Z_to_le_bytes 8 wnd) /\
  OP.rdn psegs m (Z_to_bv 64 (sa + 112)) 8 = Some (Z_to_le_bytes 8 prv) /\
  OP.rdn psegs m (Z_to_bv 64 (sa + 120)) 8 = Some (Z_to_le_bytes 8 hd).
Lemma SPTR_heap : forall LBp SPc m m' (ps : bptr) sa wnd prv hd, rheap_pres LBp SPc m m' -> In (ps, sa, FL_DSTATE_N) LBp ->
  0 <= sa -> sa + FL_DSTATE_N < 2^64 -> SPTR m sa wnd prv hd -> SPTR m' sa wnd prv hd.
Proof.
  intros LBp SPc m m' ps sa wnd prv hd HPR Is Hs Hs2 (A & Bq & C). unfold SPTR, FL_DSTATE_N in *.
  split; [| split]; (eapply (scell_heap _ _ m m' ps sa); [exact HPR| exact Is| lia| unfold FL_DSTATE_N; cbn; lia| lia| unfold FL_DSTATE_N; lia| assumption]).
Qed.

Lemma L_de4 : forall s m (pw ps pc pu : bptr) (wnd prv hd sa cp up st : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  MID [(pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m -> (st = 113 \/ st = 666) -> fm_busy FLM payload = (st =? 113) ->
  DEC m sa cp -> SPTR m sa wnd prv hd -> rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT) ->
  implM psegs (mbind (raw_free pw ;;; raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -240)) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x167f0) fc None m (seg_rom psegs)).
Proof.
  intros s m pw ps pc pu wnd prv hd sa cp up st x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 H ST B DC SP TS BY TOT.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  destruct (md_err _ _ _ _ H) as [errv ER].
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(right; left; reflexivity)) as (S1 & S2 & S3 & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 2 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 3 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in W1, W2, W3, W4, W5, S1, S2, S3, S4, S5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5. unfold FL_DSTATE_N, FL_DBLK_N in *.
  pose proof DC as (E1 & E2 & E3 & E4 & E5 & E6). pose proof SP as (P96 & P112 & P120).
  eapply implM_evt with (P := fun ms' => ms' = _).
  { eapply (fl_de_station usp ltac:(lia) SP16 0x167f0 _ 96 ltac:(do 2 right; split; reflexivity) eq_refl _ m F fc sa wnd);
      [lia| lia| exact S2| lia| exact E1| exact E2| exact E3| exact P96| reflexivity]. }
  intros ms' ->. change (0x167f0 + 0x28) with 0x16818.
  apply implM_bind_assoc.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (pw, wnd, 65536) :: ([(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) (p := pw) (A := wnd) (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -240)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -240)) in ST' by lia. rewrite ?(unsigned_lit (usp + -240)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove pw ((pw, wnd, 65536) :: ([(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB))) with ([(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB) in HPR, HEAP' by (symmetry; apply (RDriver_facts.lb_remove_head (pw, wnd, 65536)); exact ND).
  assert (H' : MID [(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ [(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] _ cl0 s s' m m' (usp + -240) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  destruct (tflush_heap _ m m' pc pu cp up HPR ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia)) as (TSh & BYh & TOTh).
  apply (L_de5 s' m' ps pc pu sa cp up st); [exact H'| exact ST| exact B| exact (DEC_heap _ _ m m' sa cp HPR ltac:(lia) DC)| exact (TSh TS)| exact (BYh BY)| exact (TOTh _ TOT)].
Qed.

Lemma L_de3 : forall s m (pv pw ps pc pu : bptr) (prv wnd hd sa cp up st : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  MID [(pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m -> (st = 113 \/ st = 666) -> fm_busy FLM payload = (st =? 113) ->
  DEC m sa cp -> SPTR m sa wnd prv hd -> rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT) ->
  implM psegs (mbind (raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -240)) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x167c8) fc None m (seg_rom psegs)).
Proof.
  intros s m pv pw ps pc pu prv wnd hd sa cp up st x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 H ST B DC SP TS BY TOT.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  destruct (md_err _ _ _ _ H) as [errv ER].
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(left; reflexivity)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 2 right; left; reflexivity)) as (S1 & S2 & S3 & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 3 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 4 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in V1, V2, V3, V4, V5, W1, W2, W3, W4, W5, S1, S2, S3, S4, S5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5. unfold FL_DSTATE_N, FL_DBLK_N in *.
  pose proof DC as (E1 & E2 & E3 & E4 & E5 & E6). pose proof SP as (P96 & P112 & P120).
  eapply implM_evt with (P := fun ms' => ms' = _).
  { eapply (fl_de_station usp ltac:(lia) SP16 0x167c8 _ 112 ltac:(right; left; split; reflexivity) eq_refl _ m F fc sa prv);
      [lia| lia| exact S2| lia| exact E1| exact E2| exact E3| exact P112| reflexivity]. }
  intros ms' ->. change (0x167c8 + 0x28) with 0x167f0.
  apply implM_bind_assoc.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (pv, prv, 65536) :: ([(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) (p := pv) (A := prv) (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -240)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -240)) in ST' by lia. rewrite ?(unsigned_lit (usp + -240)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove pv ((pv, prv, 65536) :: ([(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB))) with ([(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB) in HPR, HEAP' by (symmetry; apply (RDriver_facts.lb_remove_head (pv, prv, 65536)); exact ND).
  assert (H' : MID [(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ [(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] _ cl0 s s' m m' (usp + -240) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  destruct (tflush_heap _ m m' pc pu cp up HPR ltac:(do 3 right; left; reflexivity) ltac:(lia) ltac:(lia)) as (TSh & BYh & TOTh).
  apply (L_de4 s' m' pw ps pc pu wnd prv hd sa cp up st); [exact H'| exact ST| exact B| exact (DEC_heap _ _ m m' sa cp HPR ltac:(lia) DC)
    | exact (SPTR_heap _ _ m m' ps sa wnd prv hd HPR ltac:(right; left; reflexivity) ltac:(lia) ltac:(unfold FL_DSTATE_N; lia) SP)
    | exact (TSh TS)| exact (BYh BY)| exact (TOTh _ TOT)].
Qed.

Lemma L_de2 : forall s m (ph pv pw ps pc pu : bptr) (hd prv wnd sa cp up st : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  MID [(ph, hd, FL_DBLK_N); (pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  (st = 113 \/ st = 666) -> fm_busy FLM payload = (st =? 113) ->
  DEC m sa cp -> SPTR m sa wnd prv hd -> rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT) ->
  implM psegs (mbind (raw_free ph ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -240)) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x167a0) fc None m (seg_rom psegs)).
Proof.
  intros s m ph pv pw ps pc pu hd prv wnd sa cp up st x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 H ST B DC SP TS BY TOT.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  destruct (md_err _ _ _ _ H) as [errv ER].
  pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(left; reflexivity)) as (J1 & J2 & J3 & J4 & J5).
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 3 right; left; reflexivity)) as (S1 & S2 & S3 & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 4 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 5 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in J1, J2, J3, J4, J5, V1, V2, V3, V4, V5, W1, W2, W3, W4, W5, S1, S2, S3, S4, S5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  pose proof DC as (E1 & E2 & E3 & E4 & E5 & E6). pose proof SP as (P96 & P112 & P120).
  eapply implM_evt with (P := fun ms' => ms' = _).
  { eapply (fl_de_station usp ltac:(lia) SP16 0x167a0 _ 120 ltac:(left; split; reflexivity) eq_refl _ m F fc sa hd);
      [lia| lia| exact S2| lia| exact E1| exact E2| exact E3| exact P120| reflexivity]. }
  intros ms' ->. change (0x167a0 + 0x28) with 0x167c8.
  apply implM_bind_assoc.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (ph, hd, 65536) :: ([(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) (p := ph) (A := hd) (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -240)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -240)) in ST' by lia. rewrite ?(unsigned_lit (usp + -240)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove ph ((ph, hd, 65536) :: ([(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB))) with ([(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB) in HPR, HEAP' by (symmetry; apply (RDriver_facts.lb_remove_head (ph, hd, 65536)); exact ND).
  assert (H' : MID [(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ [(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] _ cl0 s s' m m' (usp + -240) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  destruct (tflush_heap _ m m' pc pu cp up HPR ltac:(do 4 right; left; reflexivity) ltac:(lia) ltac:(lia)) as (TSh & BYh & TOTh).
  apply (L_de3 s' m' pv pw ps pc pu prv wnd hd sa cp up st); [exact H'| exact ST| exact B| exact (DEC_heap _ _ m m' sa cp HPR ltac:(lia) DC)
    | exact (SPTR_heap _ _ m m' ps sa wnd prv hd HPR ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(unfold FL_DSTATE_N; lia) SP)
    | exact (TSh TS)| exact (BYh BY)| exact (TOTh _ TOT)].
Qed.

Lemma L_de1 : forall s m (ppb ph pv pw ps pc pu : bptr) (pb hd prv wnd sa cp up st rc2 : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  MID [(ppb, pb, FL_DBLK_N); (ph, hd, FL_DBLK_N); (pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  (st = 113 \/ st = 666) -> fm_busy FLM payload = (st =? 113) -> (rc2 = 0 \/ rc2 = 1) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -144)) 8 = Some (Z_to_le_bytes 8 sa) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 FL_ZCALLOC) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 FL_ZCFREE) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0) ->
  OP.rdn psegs m (Z_to_bv 64 sa) 8 = Some (Z_to_le_bytes 8 (usp + -200)) ->
  OP.rdn psegs m (Z_to_bv 64 (sa + 8)) 4 = Some (Z_to_le_bytes 4 st) ->
  OP.rdn psegs m (Z_to_bv 64 (sa + 16)) 8 = Some (Z_to_le_bytes 8 pb) ->
  SPTR m sa wnd prv hd -> rw_cells psegs m (usp + -88) (TSV s3 up cp n) -> bytes_at psegs m cp (map (Z_to_bv 8) cmp) ->
  OP.rdn psegs m (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT) ->
  implM psegs (mbind (raw_free ppb ;;; raw_free ph ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 rc2) x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 3) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16090) fc None m (seg_rom psegs)).
Proof.
  intros s m ppb ph pv pw ps pc pu pb hd prv wnd sa cp up st rc2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
         H ST B RC C1 C2 C3 C4 C5 C6 C7 SP TS BY TOT.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof cmp_len as CML.
  pose proof (MID_blk _ _ _ _ (ppb, pb, FL_DBLK_N) H ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5).
  pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (J1 & J2 & J3 & J4 & J5).
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 3 right; left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 4 right; left; reflexivity)) as (S1 & S2 & S3 & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 5 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 6 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5, J1, J2, J3, J4, J5, V1, V2, V3, V4, V5, W1, W2, W3, W4, W5, S1, S2, S3, S4, S5, Q1, Q2, Q3, Q4, Q5, K1, K2, K3, K4, K5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  eapply implM_evt with (P := fun ms' => exists m1 (y14 y15 : word),
      ms' = MS (mkR (Z_to_bv 64 0x167a0) (Z_to_bv 64 (usp + -240)) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200))
                     (Z_to_bv 64 pb) (Z_to_bv 64 pb) (Z_to_bv 64 sa) (Z_to_bv 64 FL_ZCFREE) y14 y15 x16 x17
                     x18 (Z_to_bv 64 3) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x2397c) fc None m1 (seg_rom psegs)
      /\ MID [(ppb, pb, 65536); (ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s m1
      /\ DEC m1 sa cp /\ SPTR m1 sa wnd prv hd /\ rw_cells psegs m1 (usp + -88) (TSV s3 up cp n) /\ bytes_at psegs m1 cp (map (Z_to_bv 8) cmp)
      /\ OP.rdn psegs m1 (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 cDTOT)).
  { unfold FL_ZCFREE, FL_ZCALLOC in *.
    eapply (fl_seg_de usp ltac:(lia) SP16 _ cp sa pb st rc2 lo m F fc);
      [lia| lia| lia| lia| lia| exact S2| lia| exact ST| exact RC| apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)
      | exact C1| exact C2| exact C3| exact C4| exact C5| exact C6| exact C7|].
    intros M1 y14 y15 pad MU WM MI1 ST1 FR1. exists M1, y14, y15. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    assert (OUTs : forall x, usp - 208 <= x \/ x < usp - 240 -> outside [(usp + -240, usp + -208)] x) by (intros x Hx; cbn; lia).
    split; [eapply (MID_munch _ _ s m M1 _ H MU WM MI1); apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]|].
    split. { unfold DEC. split; [| split; [| split; [| split; [| split]]]].
      - eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply OUTs; cbn in Hx; lia| lia| cbn; lia| exact C1].
      - eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply OUTs; cbn in Hx; lia| lia| cbn; lia| exact C3].
      - eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply OUTs; cbn in Hx; lia| lia| cbn; lia| exact C4].
      - cell_fact FR1 24%nat.
      - cell_fact FR1 16%nat.
      - cell_fact FR1 8%nat. }
    split. { destruct SP as (P96 & P112 & P120). unfold SPTR. split; [| split].
      - eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply OUTs; cbn in Hx; lia| lia| cbn; lia| exact P96].
      - eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply OUTs; cbn in Hx; lia| lia| cbn; lia| exact P112].
      - eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply OUTs; cbn in Hx; lia| lia| cbn; lia| exact P120]. }
    split; [eapply rw_cells_magree; [exact SO| exact TS|]; intros a Ha; apply OUTs; cbn in Ha; lia|].
    split; [eapply bytes_at_magree; [exact SO| exact BY|]; intros a Ha; rewrite length_map in Ha; apply OUTs; lia|].
    eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply OUTs; cbn in Hx; lia| lia| cbn; lia| exact TOT]. }
  intros ms' (m1 & y14 & y15 & -> & H1 & DC & SP1 & TS1 & BY1 & TOT1). clear C1 C2 C3 C4 C5 C6 C7 SP TS BY TOT. rename H into H0. rename H1 into H.
  destruct (md_err _ _ _ _ H) as [errv ER].
  apply implM_bind_assoc.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := (ppb, pb, 65536) :: ([(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) (p := ppb) (A := pb) (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -240)) by lia.
    - exact (md_heap _ _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp + -240)) in ST' by lia. rewrite ?(unsigned_lit (usp + -240)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ _ H)) as ND.
  replace (lb_remove ppb ((ppb, pb, 65536) :: ([(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB))) with ([(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB) in HPR, HEAP' by (symmetry; apply (RDriver_facts.lb_remove_head (ppb, pb, 65536)); exact ND).
  assert (H' : MID [(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ [(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] _ cl0 s s' m1 m' (usp + -240) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b Hb; left; split; [right; exact Hb| apply in_or_app; left; exact Hb]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  destruct (tflush_heap _ m1 m' pc pu cp up HPR ltac:(do 5 right; left; reflexivity) ltac:(lia) ltac:(lia)) as (TSh & BYh & TOTh).
  apply (L_de2 s' m' ph pv pw ps pc pu hd prv wnd sa cp up st); [exact H'| exact ST| exact B| exact (DEC_heap _ _ m1 m' sa cp HPR ltac:(lia) DC)
    | exact (SPTR_heap _ _ m1 m' ps sa wnd prv hd HPR ltac:(do 3 right; left; reflexivity) ltac:(lia) ltac:(unfold FL_DSTATE_N; lia) SP1)
    | exact (TSh TS1)| exact (BYh BY1)| exact (TOTh _ TOT1)].
Qed.

Lemma zs_same_on : forall (P : Z -> Prop) m m' inp ai outp ao z sa,
  same_on P m m' -> (forall x, usp - 200 <= x < usp - 96 -> P x) ->
  zs_cells (fl_msga CT) m (usp + -200) inp ai outp ao z sa FL_ZCALLOC FL_ZCFREE ->
  zs_cells (fl_msga CT) m' (usp + -200) inp ai outp ao z sa FL_ZCALLOC FL_ZCFREE.
Proof.
  intros P m m' inp ai outp ao z sa SO HP ((C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96) & C88).
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  unfold zs_cells, izs_cells. repeat split.
  all: first [ eapply (cell8_same_on P m m'); [exact SO| | | | eassumption]; [| lia| lia]; intros x Hx; apply HP; lia
             | eapply (cell4_same_on P m m'); [exact SO| | | | eassumption]; [| lia| lia]; intros x Hx; apply HP; lia ].
Qed.

Lemma drep_munch : forall W m m1 sa wnd prv hd pb ds,
  fl_drep CT m (DP (usp + -200) sa wnd prv hd pb) ds -> munch W m m1 ->
  (forall x, sa <= x < sa + 5968 \/ wnd <= x < wnd + 65536 \/ prv <= x < prv + 65536 \/ hd <= x < hd + 65536 \/ pb <= x < pb + 65536 -> outside W x) ->
  fl_drep CT m1 (DP (usp + -200) sa wnd prv hd pb) ds.
Proof.
  intros W m m1 sa wnd prv hd pb ds DR MU HO. apply (fl_drep_frame CT m m1 _ ds DR).
  intros a b k Hin Ha. unfold dblocks in Hin. cbn [dp_s dp_wnd dp_prv dp_hd dp_pb] in Hin. unfold FL_DSTATE_N, FL_DBLK_N in Hin.
  apply MU. apply HO.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
Qed.

Lemma bytes_at_cat : forall (m : mem) a (l1 l2 : list Z),
  bytes_at psegs m a (map (Z_to_bv 8) l1) -> bytes_at psegs m (a + Z.of_nat (length l1)) (map (Z_to_bv 8) l2) ->
  bytes_at psegs m a (map (Z_to_bv 8) (l1 ++ l2)).
Proof.
  intros m a l1 l2 (Ha & Hl1 & H1) (Ha2 & Hl2 & H2). rewrite length_map in Hl1, H1, Hl2, H2. rewrite map_app.
  split; [lia|]. split; [rewrite length_app, !length_map; lia|].
  intros i Hi. rewrite length_app, !length_map in Hi. destruct (Nat.ltb_spec0 i (length l1)).
  - rewrite nth_error_app1 by (rewrite length_map; lia). apply H1. lia.
  - rewrite nth_error_app2 by (rewrite length_map; lia). rewrite length_map.
    replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia. apply H2. lia.
Qed.
Lemma bytes_at_uncat : forall (m : mem) a (l1 l2 : list Z),
  bytes_at psegs m a (map (Z_to_bv 8) (l1 ++ l2)) ->
  bytes_at psegs m a (map (Z_to_bv 8) l1) /\ bytes_at psegs m (a + Z.of_nat (length l1)) (map (Z_to_bv 8) l2).
Proof. intros m a l1 l2 H. rewrite map_app in H. apply bytes_at_app in H. rewrite length_map in H. exact H. Qed.
Lemma bytes_at_of_holds : forall (m : mem) a (l : list Z), OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m a l -> 0 <= a -> a + Z.of_nat (length l) <= 2^64 ->
  bytes_at psegs m a (map (Z_to_bv 8) l).
Proof.
  intros m a l H Ha Hl. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds in H.
  pose proof (bytes_at_of_rdn m (length l) a _ H Ha Hl) as X. exact X.
Qed.
Lemma split3 : forall (l : list Z) k, (k < length l)%nat -> l = firstn k l ++ [nth k l 0] ++ skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|]. f_equal. apply IH. lia. Qed.
Lemma length_LC1 : Z.of_nat (length cDOUT1) = cDNOUT1 -> 0 <= cDNOUT1 <= cl0 -> Z.of_nat (length cLC1) = cl0.
Proof. intros E R. unfold LC1. rewrite length_app, repeat_length. change (ZI.zlength payload) with n. lia. Qed.
Lemma length_LC1' : Z.of_nat (length cLC1) = cl0 -> Z.of_nat (length cLC1') = cl0.
Proof. intros E. pose proof cl_range. unfold LC1'. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. Qed.

Lemma L_dfl2 : forall s m (ppb ph pv pw ps pc pu : bptr) (pb hd prv wnd sa cp up : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(ppb, pb, FL_DBLK_N); (ph, hd, FL_DBLK_N); (pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  rw_cells psegs m (usp + -88) (TSV s3 up cp n) ->
  0 <= cDNIN1 <= 3 -> 0 <= cDNOUT1 <= cl0 -> Z.of_nat (length cDOUT1) = cDNOUT1 ->
  fl_drep CT m (DP (usp + -200) sa wnd prv hd pb) cDX1 ->
  zs_cells (fl_msga CT) m (usp + -200) (D + cDNIN1) (3 - cDNIN1) (cp + cDNOUT1) (cl0 - cDNOUT1) cDZR1 sa FL_ZCALLOC FL_ZCFREE ->
  bytes_at psegs m cp (map (Z_to_bv 8) cLC1) ->
  implM psegs (mbind (raw_free ppb ;;; raw_free ph ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 n) (Z_to_bv 64 3) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16064) fc None m (seg_rom psegs)).
Proof.
  intros s m ppb ph pv pw ps pc pu pb hd prv wnd sa cp up x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TS NIN NOUT LOUT DR ZS BY.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof atop_range as AR.
  assert (ZN : ZI.zlength payload = n) by reflexivity.
  pose proof (MID_blk _ _ _ _ (ppb, pb, FL_DBLK_N) H ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & _).
  pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (J1 & J2 & J3 & J4 & _).
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (V1 & V2 & V3 & V4 & _).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 3 right; left; reflexivity)) as (W1 & W2 & W3 & W4 & _).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 4 right; left; reflexivity)) as (S1 & S2 & S3 & S4 & _).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 5 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 6 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, J1, J2, J3, J4, V1, V2, V3, V4, W1, W2, W3, W4, S1, S2, S3, S4, Q1, Q2, Q3, Q4, K1, K2, K3, K4, K5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP.
  pose proof (length_LC1 LOUT NOUT) as LL1. pose proof (length_LC1' LL1) as LL1'.
  assert (L3 : (3 < length cLC1)%nat) by lia.
  pose proof (split3 cLC1 3 L3) as SPL.
  assert (BYs : bytes_at psegs m cp (map (Z_to_bv 8) (firstn 3 cLC1 ++ [cB3] ++ skipn 4 cLC1))) by (rewrite <- SPL; exact BY).
  destruct (bytes_at_uncat m cp _ _ BYs) as [BY3 BYr0]. destruct (bytes_at_uncat m _ _ _ BYr0) as [BYb BYr]. clear BYs BYr0.
  rewrite length_firstn, Nat.min_l in BYb, BYr by lia. cbn [length map] in BYr. replace (cp + Z.of_nat 3 + Z.of_nat 1) with (cp + 4) in BYr by lia.
  replace (Z.of_nat 3) with 3 in BYb by reflexivity.
  pose proof (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) (pc, cp, cl0) ltac:(do 6 right; left; reflexivity)) as WRC. cbn [blk_addr blk_size fst snd] in WRC.
  assert (CH : rw_cells psegs m cp [CB 3 (map (Z_to_bv 8) (firstn 3 cLC1)); C1 (Z_to_bv 8 (cB3 mod 256))]).
  { split; [split|].
    - cbn. rewrite length_map, length_firstn. split; [lia| split; exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite (Z_to_bv8_mod (cB3 mod 256) cB3) by (rewrite Z.mod_mod by lia; reflexivity).
      replace (map (Z_to_bv 8) (firstn 3 cLC1) ++ [Z_to_bv 8 cB3]) with (map (Z_to_bv 8) (firstn 3 cLC1 ++ [cB3])) by (rewrite map_app; reflexivity).
      apply bytes_at_cat; [exact BY3| rewrite length_firstn, Nat.min_l by lia; exact BYb].
    - cbn [cells_size csize]. eapply wr_at_sub; [exact WRC| lia| lia| lia]. }
  eapply implM_evt with (P := fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 0x16090) (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp)
                     (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 4) x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 (n - 3)) (Z_to_bv 64 3) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x16f84) fc None m1 (seg_rom psegs)
      /\ MID [(ppb, pb, 65536); (ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s m1
      /\ rw_cells psegs m1 (usp + -88) (TSV s3 up cp n)
      /\ fl_drep CT m1 (DP (usp + -200) sa wnd prv hd pb) cDX1
      /\ zs_cells (fl_msga CT) m1 (usp + -200) (D + cDNIN1) (n - 3) (cp + cDNOUT1) (cl0 - cDNOUT1) cDZR1 sa FL_ZCALLOC FL_ZCFREE
      /\ bytes_at psegs m1 cp (map (Z_to_bv 8) cLC1')).
  { eapply (fl_seg_d2 usp ltac:(lia) SP16 _ n cp cl0 (cB3 mod 256) lo (map (Z_to_bv 8) (firstn 3 cLC1)) m F fc);
      [lia| lia| exact NR| lia| lia| lia| apply Z.mod_pos_bound; lia| apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)| exact CH|].
    intros M1 MU WM MI1 ST1 CH1 RAI. exists M1. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    split. { eapply (MID_munch _ _ s m M1 _ H MU WM MI1).
             apply Forall_cons; [right; exists (pc, cp, cl0); split; [do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
             apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
    split; [eapply rw_cells_magree; [exact SO| exact TS|]; intros a Ha; cbn in Ha; cbn; lia|].
    split. { pose proof AP as AP'. cbn [rev map app blk_addr blk_size fst snd] in AP'. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP'.
  destruct AP' as ((_ & _ & _ & _ & _ & _ & _ & _) & (_ & KS & KW & KV & KJ & KB & _) & (_ & _ & _ & _ & _ & _) & (_ & _ & _ & _ & _) & (_ & _ & _ & _) & (_ & _ & _) & (_ & _) & _).
             apply (drep_munch _ m M1 sa wnd prv hd pb cDX1 DR MU). intros x Hx. cbn. clear - Hx KS KW KV KJ KB S4 W4 V4 J4 B4 U1 U3 AR K1 CLR. lia. }
    split. { destruct ZS as ((C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96) & C88). unfold zs_cells, izs_cells.
             assert (HO : forall x, usp - 200 <= x < usp - 96 -> ~ (usp - 192 <= x < usp - 188) -> outside [(cp + 3, cp + 4); (usp + -192, usp + -188)] x)
               by (intros x Hx Hn; cbn; clear - Hx Hn K4 CLR U1 U3 AR; lia).
             split; [| unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 in *; eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply HO; cbn in Hx; lia| lia| cbn; lia| exact C88]].
             split; [eapply (cell8_same_on _ m M1); [exact SO| intros x Hx; apply HO; lia| lia| lia| exact C0]|].
             split; [unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4; replace (usp + -200 + 8) with (usp + -192) by lia; exact RAI|].
             repeat split.
             all: first [ eapply (cell8_same_on _ m M1); [exact SO| | | | eassumption]; [intros x Hx; apply HO; lia| lia| lia]
                        | eapply (cell4_same_on _ m M1); [exact SO| | | | eassumption]; [intros x Hx; apply HO; lia| lia| lia] ]. }
    unfold LC1'. replace (firstn 3 cLC1 ++ [(cB3 + 1) mod 256] ++ skipn 4 cLC1) with ((firstn 3 cLC1 ++ [(cB3 + 1) mod 256]) ++ skipn 4 cLC1) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_cat.
    - destruct CH1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. rewrite map_app. cbn [map].
      rewrite (Z_to_bv8_mod ((cB3 + 1) mod 256) (cB3 mod 256 + 1)); [exact HB|].
      rewrite Z.mod_mod by lia. rewrite <- Zplus_mod_idemp_l. reflexivity.
    - rewrite length_app, length_firstn, Nat.min_l by lia. cbn [length]. replace (cp + Z.of_nat (3 + 1)) with (cp + 4) by lia.
      eapply bytes_at_magree; [exact SO| exact BYr|]. intros a Ha. rewrite length_map, length_skipn in Ha. cbn. clear - Ha LL1 K4 U1 U3 AR CLR. lia. }
  intros ms' (m1 & -> & H1 & TS1 & DR1 & ZS1 & BY1). clear CH BY3 BYb BYr WRC DR ZS BY TS. rename H into H0. rename H1 into H.
  pose proof (slice_length payload cDNIN1 (n - 3) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as LEN.
  pose proof (holds_slice m1 D payload cDNIN1 (n - 3) (md_pay _ _ _ _ H) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as HLD.
  pose proof (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) (pc, cp, cl0) ltac:(do 6 right; left; reflexivity)) as WRC. cbn [blk_addr blk_size fst snd] in WRC.
  eapply implM_evt with (P := fun ms' => exists m' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      OF.frame_mod m1 m' [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112); (Z_to_bv 64 (cp + cDNOUT1), cDNOUT2);
                          (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)] /\
      0 <= cDRC2 <= 1 /\ 0 <= cDNOUT2 <= cl0 - cDNOUT1 /\
      fl_drep CT m' (DP (usp + -200) sa wnd prv hd pb) cDX2 /\
      zs_cells (fl_msga CT) m' (usp + -200) (D + cDNIN1 + ZDS.cs_next_in (ZDS.ds_strm cDX2)) (ZI.zlength (ZI.zc_input cDZC2) - ZDS.cs_next_in (ZDS.ds_strm cDX2))
               (cp + cDNOUT1 + cDNOUT2) (cl0 - cDNOUT1 - cDNOUT2) cDZR2 sa FL_ZCALLOC FL_ZCFREE /\
      OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m' (cp + cDNOUT1) cDOUT2 /\
      ms' = MS (mkR y1 (Z_to_bv 64 (usp + -208)) gp tp y5 y6 y7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 cDRC2) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 (n - 3)) (Z_to_bv 64 3) s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (Z_to_bv 64 0x16090) fc None m' (seg_rom psegs)).
  { eapply (dfl_evt FLIB F fc _ m1 (usp + -200) sa wnd prv hd pb (usp + -208) 0x16090 (D + cDNIN1) (cp + cDNOUT1) ATOP 4 cDX1 cDZC2).
    - split; [lia| reflexivity].
    - exact U4.
    - lia.
    - lia.
    - lia.
    - unfold OL.blocks_ok, OL.dblocks. cbn [OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ps sa 5968 H ltac:(do 4 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ pw wnd 65536 H ltac:(do 3 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ pv prv 65536 H ltac:(do 2 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ph hd 65536 H ltac:(right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ppb pb 65536 H ltac:(left; reflexivity))| apply Forall_nil].
    - exact (MID_ro _ _ _ _ H).
    - lia.
    - lia.
    - pose proof SP16 as X. apply Z.mod_divide in X; [|lia]. destruct X as [k Hk]. rewrite Hk. replace (k * 16 + -200) with ((2 * k - 25) * 8) by lia. apply Z_mod_mult.
    - lia.
    - lia.
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - cbn [ZI.zc_avail_out cDZC2 DZC2]. change (ZI.zlength payload) with n.
      pose proof (wr_at_store_ok psegs m1 cp cl0 cDNOUT1 (Z.to_nat (cl0 - cDNOUT1)) WRC ltac:(lia) ltac:(lia)) as X. exact X.
    - rewrite LEN. cbn [ZI.zc_avail_out cDZC2 DZC2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.dblocks OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb app].
      change (ZI.zlength payload) with n. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N.
      pose proof AP as AP'. cbn [rev map app blk_addr blk_size fst snd] in AP'. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP'.
  destruct AP' as ((DK & _ & DSa & DW & DV & DJ & DB & _) & (_ & KS & KW & KV & KJ & KB & _) & (_ & _ & _ & _ & _ & _) & (SW & SV & SJ & SB & _) & (WV & WJ & WBb & _) & (VJ & VB & _) & (JB & _) & _).
      split.
      { split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - DK U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KS U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KW U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KV U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KJ U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KB U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - DSa U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DW U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DV U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DJ U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DB U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - SW U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - SV U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - SJ U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - SB U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - WV U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - WJ U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - WBb U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - VJ U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - VB U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - JB U1 U3 AR DT D0 N0 CLR NOUT NIN ZN LEN K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      {  exact I. }
      exact I.
    - cbn [ZI.zc_avail_out cDZC2 DZC2 OL.dblocks OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb app]. change (ZI.zlength payload) with n.
      pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 4 right; left; reflexivity)) as (_ & _ & _ & _ & S5).
      pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 3 right; left; reflexivity)) as (_ & _ & _ & _ & W5).
      pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (_ & _ & _ & _ & V5).
      pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (_ & _ & _ & _ & J5).
      pose proof (MID_blk _ _ _ _ (ppb, pb, FL_DBLK_N) H ltac:(left; reflexivity)) as (_ & _ & _ & _ & B5).
      cbn [blk_addr blk_size fst snd] in S5, W5, V5, J5, B5. unfold FL_DSTATE_N, FL_DBLK_N in S5, W5, V5, J5, B5.
      intros a k Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; unfold FL_DSTATE_N, FL_DBLK_N;
        first [clear - U1 U3 AR; lia| clear - K5 NOUT CLR; lia| clear - S5; lia| clear - W5; lia| clear - V5; lia| clear - J5; lia| clear - B5; lia].
    - rewrite LEN. lia.
    - cbn [ZI.zc_avail_out cDZC2 DZC2]. change (ZI.zlength payload) with n. lia.
    - exact DR1.
    - exact HLD.
    - rewrite LEN. exact ZS1.
    - exact (lk_ds2 _ _ _ _ LNK0).
    - intros m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 FM RC NO NI DR' ZS' HLD'.
      exists m', y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      split. { unfold OL.dblocks, OL.wz in FM. cbn [OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb map fst snd app] in FM.
               replace (usp + -208 - FL_FRA) with (usp + -208 - 1024) in FM by reflexivity. exact FM. }
      split; [exact RC|]. split; [exact NO|]. split; [exact DR'|]. split; [exact ZS'|]. split; [exact HLD'| reflexivity]. }
  intros ms' (m' & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FM & RC & NO2 & DR2 & ZS2 & HLD2 & ->).
  assert (FPOK : Forall (fp_ok [(ppb, pb, 65536); (ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)])
             (fm_ivs [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112); (Z_to_bv 64 (cp + cDNOUT1), cDNOUT2);
                      (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)])).
  { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; exists (pc, cp, cl0); split; [do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ps, sa, 5968); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pw, wnd, 65536); split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pv, prv, 65536); split; [do 2 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ph, hd, 65536); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ppb, pb, 65536); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_nil. }
  pose proof (MID_fm _ _ s m1 m' _ H FM FPOK) as H'.
  pose proof (same_on_frame_mod _ _ _ FM) as SO.
  assert (OUT : forall x, (usp - 88 <= x < usp - 48) \/ (cp <= x < cp + cDNOUT1) \/ (cp + cDNOUT1 + cDNOUT2 <= x < cp + cl0) ->
            outside (fm_ivs [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112); (Z_to_bv 64 (cp + cDNOUT1), cDNOUT2);
                      (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)]) x).
  { pose proof AP as AP'. cbn [rev map app blk_addr blk_size fst snd] in AP'. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP'.
  destruct AP' as ((_ & _ & _ & _ & _ & _ & _ & _) & (_ & KS & KW & KV & KJ & KB & _) & (_ & _ & _ & _ & _ & _) & (_ & _ & _ & _ & _) & (_ & _ & _ & _) & (_ & _ & _) & (_ & _) & _).
    intros x Hx. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by blia. clear - Hx KS KW KV KJ KB K4 S4 W4 V4 J4 B4 U1 U3 AR NOUT NO2 CLR. lia. }
  assert (TS' : rw_cells psegs m' (usp + -88) (TSV s3 up cp n)).
  { eapply rw_cells_magree; [exact SO| exact TS1|]. intros a Ha. apply OUT. left. cbn in Ha. lia. }
  assert (LOUT2 : Z.of_nat (length cDOUT2) = cDNOUT2).
  { unfold DOUT2, DNOUT2, ZDS.cs_output. rewrite List.rev_append_rev, app_nil_r, length_rev. reflexivity. }
  assert (BY' : bytes_at psegs m' cp (map (Z_to_bv 8) cmp)).
  { rewrite (lk_compr _ _ _ _ LNK0). unfold LC2. apply bytes_at_cat; [| apply bytes_at_cat].
    - eapply bytes_at_magree; [exact SO| |].
      + rewrite <- (firstn_skipn (Z.to_nat cDNOUT1) cLC1') in BY1. apply bytes_at_uncat in BY1. exact (proj1 BY1).
      + intros a Ha. rewrite length_map, length_firstn in Ha. apply OUT. right; left. clear - Ha LL1' NOUT. lia.
    - rewrite length_firstn, Nat.min_l by lia. rewrite Z2Nat.id by lia. apply (bytes_at_of_holds m' _ _ HLD2); [lia| rewrite LOUT2; lia].
    - rewrite length_firstn, Nat.min_l by lia. rewrite Z2Nat.id by lia. replace (Z.of_nat (length cDOUT2)) with cDNOUT2 by lia.
      eapply bytes_at_magree; [exact SO| |].
      + rewrite <- (firstn_skipn (Z.to_nat (cDNOUT1 + cDNOUT2)) cLC1') in BY1. apply bytes_at_uncat in BY1.
        rewrite length_firstn, Nat.min_l in BY1 by lia. rewrite Z2Nat.id in BY1 by lia. replace (cp + (cDNOUT1 + cDNOUT2)) with (cp + cDNOUT1 + cDNOUT2) in BY1 by lia. exact (proj2 BY1).
      + intros a Ha. rewrite length_map, length_skipn in Ha. apply OUT. right; right. clear - Ha LL1' NOUT NO2. lia. }
  destruct ZS2 as ((C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96) & C88).
  destruct (fl_drep_cells CT _ _ _ DR2) as (P0 & P8 & P16 & P96 & P112 & P120). cbn [dp_s dp_strm dp_pb dp_wnd dp_prv dp_hd] in P0, P8, P16, P96, P112, P120.
  unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 in *.
  apply (L_de1 s m' ppb ph pv pw ps pc pu pb hd prv wnd sa cp up (ZDS.ds_status cDX2) cDRC2);
    [exact H'| exact (lk_st2 _ _ _ _ LNK0)| exact (lk_busy _ _ _ _ LNK0)| lia
    | replace (usp + -144) with (usp + -200 + 56) by lia; exact C56
    | replace (usp + -136) with (usp + -200 + 64) by lia; exact C64
    | replace (usp + -128) with (usp + -200 + 72) by lia; exact C72
    | replace (usp + -120) with (usp + -200 + 80) by lia; exact C80
    | exact P0| exact P8| exact P16
    | split; [exact P96| split; [exact P112| exact P120]]
    | exact TS'| exact BY'
    | replace (usp + -160) with (usp + -200 + 40) by lia; exact C40].
Qed.

Definition DIC (m : mem) (sa : Z) : Prop :=
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 16) 0 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 40) 0 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 48) 0 /\
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 56) sa /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 64) FL_ZCALLOC /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 72) FL_ZCFREE /\
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 80) 0 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (usp + -200 + 88) 2 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (usp + -200 + 96) 1.
Lemma length_DOUT1 : Z.of_nat (length cDOUT1) = cDNOUT1.
Proof. unfold DOUT1, DNOUT1, ZDS.cs_output. rewrite List.rev_append_rev, app_nil_r, length_rev. reflexivity. Qed.
Lemma bytes_at_of_zeros : forall (m : mem) a k, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m a k -> 0 <= a -> 0 <= k -> a + k <= 2^64 ->
  bytes_at psegs m a (map (Z_to_bv 8) (repeat 0 (Z.to_nat k))).
Proof.
  intros m a k HZ Ha Hk Hak. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at in HZ. rewrite map_repeat.
  exact (bytes_at_of_rdn m (Z.to_nat k) a _ HZ Ha ltac:(lia)).
Qed.

Lemma L_dfl1 : forall s m (ppb ph pv pw ps pc pu : bptr) (pb hd prv wnd sa cp up : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(ppb, pb, FL_DBLK_N); (ph, hd, FL_DBLK_N); (pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  rw_cells psegs m (usp + -88) (TSV s3 up cp n) ->
  DIC m sa -> fl_drep CT m (DP (usp + -200) sa wnd prv hd pb) (fl_ds0 CT) ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (mbind (raw_free ppb ;;; raw_free ph ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 n) (Z_to_bv 64 FL_DATALEN) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16028) fc None m (seg_rom psegs)).
Proof.
  intros s m ppb ph pv pw ps pc pu pb hd prv wnd sa cp up x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TS DC DR ZC.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof atop_range as AR.
  assert (ZN : ZI.zlength payload = n) by reflexivity.
  pose proof (MID_blk _ _ _ _ (ppb, pb, FL_DBLK_N) H ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & _).
  pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (J1 & J2 & J3 & J4 & _).
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (V1 & V2 & V3 & V4 & _).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 3 right; left; reflexivity)) as (W1 & W2 & W3 & W4 & _).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 4 right; left; reflexivity)) as (S1 & S2 & S3 & S4 & _).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 5 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 6 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, J1, J2, J3, J4, V1, V2, V3, V4, W1, W2, W3, W4, S1, S2, S3, S4, Q1, Q2, Q3, Q4, K1, K2, K3, K4, K5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP.
  destruct (md_hf _ _ _ _ H) as [pad HFc]. pose proof (md_st _ _ _ _ H) as STc. unfold HDATA in STc.
  eapply implM_evt with (P := fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 0x16064) (Z_to_bv 64 (usp + -208)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp)
                     (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 3) x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 n) (Z_to_bv 64 3) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x16f84) fc None m1 (seg_rom psegs)
      /\ MID [(ppb, pb, 65536); (ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s m1
      /\ rw_cells psegs m1 (usp + -88) (TSV s3 up cp n)
      /\ fl_drep CT m1 (DP (usp + -200) sa wnd prv hd pb) (fl_ds0 CT)
      /\ zs_cells (fl_msga CT) m1 (usp + -200) D 3 cp cl0 DZS0 sa FL_ZCALLOC FL_ZCFREE
      /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m1 cp cl0).
  { eapply (fl_seg_d1 usp ltac:(lia) SP16 _ D n cp cl0 lo m F fc);
      [lia| lia| lia| lia| lia| apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)| cell_fact STc 8%nat
      | unfold LFC in HFc; replace (usp + -40) with (usp - 48 + 8) by lia; cell_fact HFc 8%nat|].
    intros M1 MU WM MI1 ST1 R1 R2 R3 R4. exists M1. split; [reflexivity|].
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    assert (HO : forall x, (x < usp - 200 \/ usp - 164 <= x \/ (usp - 188 <= x < usp - 176)) -> outside [(usp + -200, usp + -188); (usp + -176, usp + -164)] x)
      by (intros x Hx; cbn; clear - Hx; lia).
    split; [eapply (MID_munch _ _ s m M1 _ H MU WM MI1); apply Forall_cons; [left; cbn [fst snd]; lia|]; apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]|].
    split; [eapply rw_cells_magree; [exact SO| exact TS|]; intros a Ha; apply HO; cbn in Ha; lia|].
    split; [apply (drep_munch _ m M1 sa wnd prv hd pb (fl_ds0 CT) DR MU); intros x Hx; apply HO; left; clear - Hx S4 W4 V4 J4 B4 U1 U3 AR; lia|].
    split.
    { destruct DC as (C16 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96). unfold zs_cells, izs_cells.
      cbn [ZI.zs_total_in ZI.zs_total_out ZI.zs_msg ZI.zs_adler ZI.zs_data_type DZS0]. rewrite (fl_msga_null CT). unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 in *.
      split; [| eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply HO; lia| lia| cbn; lia| exact C88]].
      split; [replace (usp + -200) with (usp + -200 + 0) by lia; replace (usp + -200 + 0) with (usp + -200) by lia; exact R1|].
      split; [replace (usp + -200 + 8) with (usp + -192) by lia; exact R2|].
      split; [eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply HO; lia| lia| cbn; lia| exact C16]|].
      split; [replace (usp + -200 + 24) with (usp + -176) by lia; exact R3|].
      split; [replace (usp + -200 + 32) with (usp + -168) by lia; exact R4|].
      repeat split; (eapply (rdn_same_on8 _ m M1 _ _ _ SO); [intros x Hx; apply HO; lia| lia| cbn; lia| assumption]). }
    eapply zeros_at_same_on; [exact SO| intros x Hx; apply HO; left; clear - Hx K4 U1 U3 AR; lia| lia| lia| lia| exact ZC]. }
  intros ms' (m1 & -> & H1 & TS1 & DR1 & ZS1 & ZC1). clear DC DR ZC TS HFc STc. rename H into H0. rename H1 into H.
  assert (LEN : ZI.zlength (ZI.zc_input (DZC1 payload)) = 3). { cbn [ZI.zc_input DZC1]. unfold ZI.zlength. rewrite length_firstn. pose proof NR as NR'. unfold zlength in NR'. lia. }
  pose proof NR as NR'. unfold zlength in NR'.
  pose proof (holds_slice m1 D payload 0 3 (md_pay _ _ _ _ H) ltac:(lia) ltac:(lia) ltac:(lia)) as HLD. rewrite Z.add_0_r in HLD. cbn [Z.to_nat skipn] in HLD.
  pose proof (proj1 (Forall_forall _ _) (md_wr _ _ _ _ H) (pc, cp, cl0) ltac:(do 6 right; left; reflexivity)) as WRC. cbn [blk_addr blk_size fst snd] in WRC.
  eapply implM_evt with (P := fun ms' => exists m' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      OF.frame_mod m1 m' [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112); (Z_to_bv 64 cp, cDNOUT1);
                          (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)] /\
      0 <= cDNOUT1 <= cl0 /\ 0 <= cDNIN1 <= 3 /\
      fl_drep CT m' (DP (usp + -200) sa wnd prv hd pb) cDX1 /\
      zs_cells (fl_msga CT) m' (usp + -200) (D + cDNIN1) (3 - cDNIN1) (cp + cDNOUT1) (cl0 - cDNOUT1) cDZR1 sa FL_ZCALLOC FL_ZCFREE /\
      OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m' cp cDOUT1 /\
      ms' = MS (mkR y1 (Z_to_bv 64 (usp + -208)) gp tp y5 y6 y7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 cDRC1) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 n) (Z_to_bv 64 3) s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (Z_to_bv 64 0x16064) fc None m' (seg_rom psegs)).
  { eapply (dfl_evt FLIB F fc _ m1 (usp + -200) sa wnd prv hd pb (usp + -208) 0x16064 D cp ATOP 3 (fl_ds0 CT) (DZC1 payload)).
    - split; [lia| reflexivity].
    - exact U4.
    - lia.
    - lia.
    - lia.
    - unfold OL.blocks_ok, OL.dblocks. cbn [OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ps sa 5968 H ltac:(do 4 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ pw wnd 65536 H ltac:(do 3 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ pv prv 65536 H ltac:(do 2 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ph hd 65536 H ltac:(right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ppb pb 65536 H ltac:(left; reflexivity))| apply Forall_nil].
    - exact (MID_ro _ _ _ _ H).
    - lia.
    - lia.
    - pose proof SP16 as X. apply Z.mod_divide in X; [|lia]. destruct X as [k Hk]. rewrite Hk. replace (k * 16 + -200) with ((2 * k - 25) * 8) by lia. apply Z_mod_mult.
    - lia.
    - lia.
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - apply (store_ok_of_stk m1 lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - cbn [ZI.zc_avail_out DZC1]. change (ZI.zlength payload) with n.
      pose proof (wr_at_store_ok psegs m1 cp cl0 0 (Z.to_nat cl0) WRC ltac:(lia) ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X.
    - rewrite LEN. cbn [ZI.zc_avail_out DZC1 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.dblocks OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb app].
      change (ZI.zlength payload) with n. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N.
      pose proof AP as AP'. cbn [rev map app blk_addr blk_size fst snd] in AP'. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP'.
  destruct AP' as ((DK & _ & DSa & DW & DV & DJ & DB & _) & (_ & KS & KW & KV & KJ & KB & _) & (_ & _ & _ & _ & _ & _) & (SW & SV & SJ & SB & _) & (WV & WJ & WBb & _) & (VJ & VB & _) & (JB & _) & _).
      split.
      { split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - DK U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KS U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KW U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KV U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KJ U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - KB U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - DSa U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DW U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DV U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DJ U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - DB U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - SW U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - SV U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - SJ U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - SB U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - WV U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - WJ U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - WBb U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - VJ U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. split; [clear - VB U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      { split; [clear - JB U1 U3 AR DT D0 N0 NR CLR K1 K4 S1 S4 W1 W4 V1 V4 J1 J4 B1 B4; lia|]. exact I. }
      split.
      {  exact I. }
      exact I.
    - cbn [ZI.zc_avail_out DZC1 OL.dblocks OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb app]. change (ZI.zlength payload) with n.
      pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 4 right; left; reflexivity)) as (_ & _ & _ & _ & S5).
      pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 3 right; left; reflexivity)) as (_ & _ & _ & _ & W5).
      pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (_ & _ & _ & _ & V5).
      pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (_ & _ & _ & _ & J5).
      pose proof (MID_blk _ _ _ _ (ppb, pb, FL_DBLK_N) H ltac:(left; reflexivity)) as (_ & _ & _ & _ & B5).
      cbn [blk_addr blk_size fst snd] in S5, W5, V5, J5, B5. unfold FL_DSTATE_N, FL_DBLK_N in S5, W5, V5, J5, B5.
      intros a k Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; unfold FL_DSTATE_N, FL_DBLK_N;
        first [clear - U1 U3 AR; lia| clear - K5 CLR; lia| clear - S5; lia| clear - W5; lia| clear - V5; lia| clear - J5; lia| clear - B5; lia].
    - rewrite LEN. lia.
    - cbn [ZI.zc_avail_out DZC1]. change (ZI.zlength payload) with n. lia.
    - exact DR1.
    - exact HLD.
    - rewrite LEN. exact ZS1.
    - exact (lk_ds1 _ _ _ _ LNK0).
    - intros m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 FM RC NO NI DR' ZS' HLD'.
      exists m', y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      rewrite LEN in NI, ZS'. cbn [ZI.zc_avail_out DZC1] in NO, ZS'. change (ZI.zlength payload) with n in NO, ZS'.
      split. { unfold OL.dblocks, OL.wz in FM. cbn [OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb map fst snd app] in FM.
               replace (usp + -208 - FL_FRA) with (usp + -208 - 1024) in FM by reflexivity. exact FM. }
      split; [exact NO|]. split; [exact NI|]. split; [exact DR'|]. split; [exact ZS'|]. split; [exact HLD'| reflexivity]. }
  intros ms' (m' & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FM & NO & NI & DR2 & ZS2 & HLD2 & ->).
  rewrite (lk_rc1 _ _ _ _ LNK0).
  assert (FPOK : Forall (fp_ok [(ppb, pb, 65536); (ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)])
             (fm_ivs [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112); (Z_to_bv 64 cp, cDNOUT1);
                      (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)])).
  { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; exists (pc, cp, cl0); split; [do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ps, sa, 5968); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pw, wnd, 65536); split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pv, prv, 65536); split; [do 2 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ph, hd, 65536); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ppb, pb, 65536); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_nil. }
  pose proof (MID_fm _ _ s m1 m' _ H FM FPOK) as H'.
  pose proof (same_on_frame_mod _ _ _ FM) as SO.
  assert (OUT : forall x, (usp - 88 <= x < usp - 48) \/ (cp + cDNOUT1 <= x < cp + cl0) ->
            outside (fm_ivs [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112); (Z_to_bv 64 cp, cDNOUT1);
                      (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)]) x).
  { pose proof AP as AP'. cbn [rev map app blk_addr blk_size fst snd] in AP'. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP'.
  destruct AP' as ((_ & _ & _ & _ & _ & _ & _ & _) & (_ & KS & KW & KV & KJ & KB & _) & (_ & _ & _ & _ & _ & _) & (_ & _ & _ & _ & _) & (_ & _ & _ & _) & (_ & _ & _) & (_ & _) & _).
    intros x Hx. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. clear - Hx KS KW KV KJ KB K4 S4 W4 V4 J4 B4 U1 U3 AR NO CLR. lia. }
  assert (TS' : rw_cells psegs m' (usp + -88) (TSV s3 up cp n)).
  { eapply rw_cells_magree; [exact SO| exact TS1|]. intros a Ha. apply OUT. left. cbn in Ha. lia. }
  pose proof length_DOUT1 as LOUT.
  assert (BY' : bytes_at psegs m' cp (map (Z_to_bv 8) cLC1)).
  { unfold LC1. change (ZI.zlength payload) with n. apply bytes_at_cat.
    - apply (bytes_at_of_holds m' _ _ HLD2); [lia| rewrite LOUT; lia].
    - rewrite LOUT. eapply bytes_at_magree; [exact SO| |].
      + apply bytes_at_of_zeros; [| lia| lia| lia]. eapply (zeros_at_sub m1 cp cl0); [exact ZC1| lia| lia| lia| lia| lia].
      + intros a Ha. rewrite length_map, repeat_length in Ha. apply OUT. right. clear - Ha NO. lia. }
  apply (L_dfl2 s m' ppb ph pv pw ps pc pu pb hd prv wnd sa cp up); [exact H'| exact TS'| exact NI| exact NO| exact LOUT| exact DR2| exact ZS2| exact BY'].
Qed.

Definition in_szero (sa x : Z) : Prop :=
  sa + 12 <= x < sa + 48 \/ sa + 52 <= x < sa + 56 \/ sa + 64 <= x < sa + 80 \/ sa + 92 <= x < sa + 96 \/
  sa + 104 <= x < sa + 112 \/ sa + 128 <= x < sa + 132 \/ sa + 148 <= x < sa + 5896 \/ sa + 5900 <= x < sa + 5952 \/
  sa + 5960 <= x < sa + 5968.   (* 1.4: the state's last 8 bytes (slid) *)
Definition szero (m : mem) (sa : Z) : Prop :=
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 12) 36 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 52) 4 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 64) 16 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 92) 4 /\
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 104) 8 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 128) 4 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 148) 5748 /\ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 5900) 52 /\
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (sa + 5960) 8.   (* 1.4: 5968-byte state; high_water (5952..5959) is a cell *)
Lemma szero_same_on : forall (P : Z -> Prop) m m' sa,
  same_on P m m' -> 0 <= sa -> sa + 5968 <= 2^64 -> (forall x, in_szero sa x -> P x) -> szero m sa -> szero m' sa.
Proof.
  intros P m m' sa SO Hs Hs2 HP (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9). unfold in_szero in HP. unfold szero.
  repeat split; (eapply zeros_at_same_on; [exact SO| intros x Hx; apply HP; lia| lia| lia| lia| assumption]).
Qed.
Lemma szero_of_block : forall m sa,
  rw_cells psegs m sa [CB (Z.to_nat 5968) (repeat (Z_to_bv 8 0) (Z.to_nat 5968))] -> 0 <= sa -> sa + 5968 <= 2^64 -> szero m sa.
Proof.
  intros m sa BLK Hs Hs2. pose proof (zeros_at_of_chunk m sa 5968 BLK ltac:(lia)) as Z0. unfold szero.
  repeat split; (eapply (zeros_at_sub m sa 5968); [exact Z0| lia| lia| lia| lia| lia]).
Qed.
Lemma szero_heap : forall LBp SPc m m' (ps : bptr) sa, rheap_pres LBp SPc m m' -> In (ps, sa, 5968) LBp -> 0 <= sa -> sa + 5968 <= 2^64 ->
  szero m sa -> szero m' sa.
Proof.
  intros LBp SPc m m' ps sa HPR Is Hs Hs2 HZ. eapply szero_same_on; [exact (same_on_rheap_pres _ _ _ _ HPR)| lia| lia| | exact HZ].
  intros x Hx. right; right. exists (ps, sa, 5968). split; [exact Is| cbn [blk_addr blk_size fst snd]; unfold in_szero in Hx; lia].
Qed.
Lemma zblk_heap : forall LBp SPc m m' (pp : bptr) a k, rheap_pres LBp SPc m m' -> In (pp, a, k) LBp -> 0 <= a -> 0 < k -> a + k < 2^64 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m a k -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m' a k.
Proof.
  intros LBp SPc m m' pp a k HPR Ip Ha Hk Hak HZ. eapply zeros_at_same_on; [exact (same_on_rheap_pres _ _ _ _ HPR)| | lia| lia| lia| exact HZ].
  intros x Hx. right; right. exists (pp, a, k). split; [exact Ip| cbn [blk_addr blk_size fst snd]; lia].
Qed.
Lemma schunk_heap : forall LBp SPc m m' (ps : bptr) sa a cs, rheap_pres LBp SPc m m' -> In (ps, sa, 5968) LBp ->
  sa <= a -> a + Z.of_nat (cells_size cs) <= sa + 5968 -> rw_cells psegs m a cs -> rw_cells psegs m' a cs.
Proof.
  intros LBp SPc m m' ps sa a cs HPR Is Ha Hsz SC. eapply rw_cells_magree; [exact (same_on_rheap_pres _ _ _ _ HPR)| exact SC|].
  intros x Hx. right; right. exists (ps, sa, 5968). split; [exact Is| cbn [blk_addr blk_size fst snd]; lia].
Qed.
(* 1.4 UBSan: deflateInit2_'s 80-byte frame (sp = usp - 288) saves s7 too; DI2 is its nine saved words from
   usp - 280 (= hh - 72) up; the 8 bytes at usp - 288 are padding (fl_seg_tf1's q0) *)
Definition DI2 (cp : Z) : list cell :=
  [C8 s7; C8 s6; C8 s5; C8 s4; C8 (Z_to_bv 64 0x3d6a0); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 (usp + -40)); C8 (Z_to_bv 64 0x16028)].
Definition SCH (mid : list cell) (g12 g52 g64 g148 : list byte) : list cell :=
  [C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
   C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767)] ++ mid ++
  [C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148].

Lemma L_di : forall s m (ppb ph pv pw ps pc pu : bptr) (pb hd prv wnd sa cp up : Z)
    (p0 p96 g12 g52 g64 g92a g104a g128 g148 j3a j3b j3c : list byte)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(ppb, pb, FL_DBLK_N); (ph, hd, FL_DBLK_N); (pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  rw_cells psegs m (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) ->
  rw_cells psegs m (usp + -280) (DI2 cp) ->
  rw_cells psegs m sa (SCH [CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 8 g104a; C8 (Z_to_bv 64 prv); C8 (Z_to_bv 64 hd); CB 4 g128] g12 g52 g64 g148) ->
  rw_cells psegs m (sa + 5888) [CB 8 j3a; C4 (Z_to_bv 64 16384); CB 52 j3b; C8 (Z_to_bv 64 0); CB 8 j3c] ->
  szero m sa ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m wnd FL_DBLK_N -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m prv FL_DBLK_N -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m hd FL_DBLK_N -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m pb FL_DBLK_N ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (mbind (raw_free ppb ;;; raw_free ph ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 pb) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 FL_A_DI) fc None m (seg_rom psegs)).
Proof.
  intros s m ppb ph pv pw ps pc pu pb hd prv wnd sa cp up p0 p96 g12 g52 g64 g92a g104a g128 g148 j3a j3b j3c
         x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TD DI SC S3 ZS Zw Zp Zh Zb Zcp.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CLR. pose proof n_nonneg as N0. pose proof atop_range as AR.
  pose proof (MID_blk _ _ _ _ (ppb, pb, FL_DBLK_N) H ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & _).
  pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (J1 & J2 & J3 & J4 & _).
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (V1 & V2 & V3 & V4 & _).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 3 right; left; reflexivity)) as (W1 & W2 & W3 & W4 & _).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 4 right; left; reflexivity)) as (S1 & S2 & S3' & S4 & _).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 5 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 6 right; left; reflexivity)) as (K1 & K2 & K3 & K4 & _).
  cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, J1, J2, J3, J4, V1, V2, V3, V4, W1, W2, W3, W4, S1, S2, S3', S4, Q1, Q2, Q3, Q4, K1, K2, K3, K4.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  pose proof (MID_all_apart _ _ _ _ H ltac:(lia)) as AP.
  unfold TFC in TD. unfold DI2 in DI. unfold SCH in SC. cbn [app] in SC.
  change ([CB 56 p0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sa); C8 (Z_to_bv 64 0x1a9f4); C8 (Z_to_bv 64 0x1aa04); C8 (Z_to_bv 64 0); CB 24 p96;
           C8 s3; C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 up); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x1635c)])
    with ([CB 56 p0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sa); C8 (Z_to_bv 64 0x1a9f4); C8 (Z_to_bv 64 0x1aa04); C8 (Z_to_bv 64 0); CB 24 p96] ++ TSV s3 up cp n) in TD.
  pose proof (rw_cells_app_split m _ _ _ TD) as [TD1 TS]. change (Z.of_nat (cells_size _)) with 120 in TS.
  replace (usp + -208 + 120) with (usp + -88) in TS by lia.
  destruct ZS as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  replace (usp + -288) with (usp + -208 - 80) by lia. replace (usp + -200) with (usp + -208 + 8) by lia.
  eapply implM_evt with (P := fun ms' => exists m' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      OF.frame_mod m m' [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -208 + 8), 112);
                         (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)] /\
      DIC m' sa /\ fl_drep CT m' (DP (usp + -200) sa wnd prv hd pb) (fl_ds0 CT) /\
      ms' = MS (mkR y1 (Z_to_bv 64 (usp + -208)) gp tp y5 y6 y7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 n) (Z_to_bv 64 FL_DATALEN) s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (Z_to_bv 64 0x16028) fc None m' (seg_rom psegs)).
  { eapply (di_evt FLIB F fc _ m (usp + -208) sa wnd prv hd pb ATOP 0x16028 (usp + -40) cp n s4 s5 s6 s7).
    - exact U4.
    - lia.
    - lia.
    - lia.
    - unfold OL.blocks_ok, OL.dblocks. cbn [OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ps sa 5968 H ltac:(do 4 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ pw wnd 65536 H ltac:(do 3 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ pv prv 65536 H ltac:(do 2 right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ph hd 65536 H ltac:(right; left; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; exact (blk_okz_of_MID _ _ _ _ ppb pb 65536 H ltac:(left; reflexivity))| apply Forall_nil].
    - cbn [OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all OL.dblocks OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb]. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N.
      pose proof AP as AP'. cbn [rev map app blk_addr blk_size fst snd] in AP'. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP'.
  destruct AP' as ((_ & _ & _ & _ & _ & _ & _ & _) & (_ & _ & _ & _ & _ & _ & _) & (_ & _ & _ & _ & _ & _) & (SW & SV & SJ & SB & _) & (WV & WJ & WBb & _) & (VJ & VB & _) & (JB & _) & _).
    split.
    { split; [clear - SW S1 W1 V1 J1 B1; lia|]. split; [clear - SV S1 W1 V1 J1 B1; lia|]. split; [clear - SJ S1 W1 V1 J1 B1; lia|]. split; [clear - SB S1 W1 V1 J1 B1; lia|]. exact I. }
    split.
    { split; [clear - WV S1 W1 V1 J1 B1; lia|]. split; [clear - WJ S1 W1 V1 J1 B1; lia|]. split; [clear - WBb S1 W1 V1 J1 B1; lia|]. exact I. }
    split.
    { split; [clear - VJ S1 W1 V1 J1 B1; lia|]. split; [clear - VB S1 W1 V1 J1 B1; lia|]. exact I. }
    split.
    { split; [clear - JB S1 W1 V1 J1 B1; lia|]. exact I. }
    split.
    {  exact I. }
    exact I.
    - exact (MID_ro _ _ _ _ H).
    - apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ _ H)| lia| cbn; lia].
    - split; [lia| reflexivity].
    - lia.
    - lia.
    - lia.
    - exact Zw.
    - exact Zp.
    - exact Zh.
    - exact Zb.
    - exact Z1.
    - exact Z2.
    - exact Z3.
    - exact Z4.
    - exact Z5.
    - exact Z6.
    - exact Z7.
    - exact Z8.
    - exact Z9.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact SC 0%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 8%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 48%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact SC 56%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 80%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 84%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 88%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact SC 96%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact SC 112%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact SC 120%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 132%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 136%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 140%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact SC 144%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4. cell_fact S3 8%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact S3 64%nat.   (* 1.4: high_water at s + 5952 *)
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact DI 64%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact DI 56%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact DI 48%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact DI 40%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, OL.FL_DATALEN. cell_fact DI 32%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw. cell_fact DI 24%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw. cell_fact DI 16%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw. cell_fact DI 8%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw. cell_fact DI 0%nat.    (* 1.4: s7 at hh - 72 *)
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact TD1 56%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact TD1 64%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, OL.FL_ZCALLOC. cell_fact TD1 72%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8, OL.FL_ZCFREE. cell_fact TD1 80%nat.
    - unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8. cell_fact TD1 88%nat.
    - intros m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 FM E1 E2 E3 E4 E5 E6 E7 E8 E9 DR.
      exists m', y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      split; [exact FM|]. split; [| split; [| reflexivity]].
      + unfold DIC. replace (usp + -200) with (usp + -208 + 8) by lia.
        replace (usp + -208 + 8 + 16) with (usp + -208 + 24) by lia. replace (usp + -208 + 8 + 40) with (usp + -208 + 48) by lia.
        replace (usp + -208 + 8 + 48) with (usp + -208 + 56) by lia. replace (usp + -208 + 8 + 56) with (usp + -208 + 64) by lia.
        replace (usp + -208 + 8 + 64) with (usp + -208 + 72) by lia. replace (usp + -208 + 8 + 72) with (usp + -208 + 80) by lia.
        replace (usp + -208 + 8 + 80) with (usp + -208 + 88) by lia. replace (usp + -208 + 8 + 88) with (usp + -208 + 96) by lia.
        replace (usp + -208 + 8 + 96) with (usp + -208 + 104) by lia.
        repeat split; assumption.
      + replace (usp + -200) with (usp + -208 + 8) by lia. exact DR. }
  intros ms' (m' & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FM & DC & DR & ->).
  replace (usp + -208 + 8) with (usp + -200) in FM by lia.
  assert (FPOK : Forall (fp_ok [(ppb, pb, 65536); (ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)])
             (fm_ivs [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112);
                      (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)])).
  { unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by lia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; exists (ps, sa, 5968); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pw, wnd, 65536); split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (pv, prv, 65536); split; [do 2 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ph, hd, 65536); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; exists (ppb, pb, 65536); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_nil. }
  pose proof (MID_fm _ _ s m m' _ H FM FPOK) as H'.
  pose proof (same_on_frame_mod _ _ _ FM) as SO.
  assert (OUT : forall x, (usp - 88 <= x < usp - 48) \/ (cp <= x < cp + cl0) ->
            outside (fm_ivs [(Z_to_bv 64 (usp + -208 - 1024), 1024); (Z_to_bv 64 (usp + -200), 112);
                      (Z_to_bv 64 sa, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)]) x).
  { pose proof AP as AP'. cbn [rev map app blk_addr blk_size fst snd] in AP'. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart_from_all, OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP'.
  destruct AP' as ((_ & _ & _ & _ & _ & _ & _ & _) & (_ & KS & KW & KV & KJ & KB & _) & (_ & _ & _ & _ & _ & _) & (_ & _ & _ & _ & _) & (_ & _ & _ & _) & (_ & _ & _) & (_ & _) & _).
    intros x Hx. unfold fm_ivs. cbn [map fst snd app outside]. rewrite !unsigned_lit by lia. clear - Hx KS KW KV KJ KB K4 S4 W4 V4 J4 B4 U1 U3 AR CLR. lia. }
  apply (L_dfl1 s m' ppb ph pv pw ps pc pu pb hd prv wnd sa cp up); [exact H'| | exact DC| exact DR|].
  - eapply rw_cells_magree; [exact SO| exact TS|]. intros a Ha. apply OUT. left. cbn in Ha. lia.
  - eapply zeros_at_same_on; [exact SO| intros x Hx; apply OUT; right; exact Hx| lia| lia| lia| exact Zcp].
Qed.


Lemma L_h : forall s m (ph pv pw ps pc pu : bptr) (hd prv wnd sa cp up : Z)
    (p0 p96 g12 g52 g64 g92a g104a g120 g148 j3 : list byte)
    (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(ph, hd, FL_DBLK_N); (pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  rw_cells psegs m (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) ->
  rw_cells psegs m (usp + -280) (DI2 cp) ->
  rw_cells psegs m sa (SCH [CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 8 g104a; C8 (Z_to_bv 64 prv); CB 12 g120] g12 g52 g64 g148) ->
  rw_cells psegs m (sa + 5888) [CB 80 j3] ->
  szero m sa ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m wnd FL_DBLK_N -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m prv FL_DBLK_N -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m hd FL_DBLK_N ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (mbind (pb <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;;
                      (raw_free pb ;;; raw_free ph ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT)) (KTS pc pu)) s POST
    (MS (mkR (Z_to_bv 64 0x165fc) (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 hd) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x165fc) fc None m (seg_rom psegs)).
Proof.
  intros s m ph pv pw ps pc pu hd prv wnd sa cp up p0 p96 g12 g52 g64 g92a g104a g120 g148 j3
         x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TD DI SC S3 ZS Zw Zp Zh Zcp.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CBR. pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ _ (ph, hd, FL_DBLK_N) H ltac:(left; reflexivity)) as (K1 & K2 & K3 & K4 & K5).
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(do 2 right; left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 3 right; left; reflexivity)) as (S1 & S2 & S3' & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 4 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 5 right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5).
  cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, V1, V2, V3, V4, V5, W1, W2, W3, W4, W5, S1, S2, S3', S4, S5, Q1, Q2, Q3, Q4, Q5, R1, R2, R3, R4, R5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  unfold SCH in SC. cbn [app] in SC.
  eapply implM_evt with (P := fun ms' => exists (M1 : mem) (g128 j3a j3b j3c : list byte),
      munch [(sa + 120, sa + 128); (sa + 5896, sa + 5900); (sa + 5952, sa + 5960)] m M1 /\ wmono psegs m M1 /\ mem_inv psegs M1 /\
      rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) /\
      rw_cells psegs M1 sa (SCH [CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 8 g104a; C8 (Z_to_bv 64 prv); C8 (Z_to_bv 64 hd); CB 4 g128] g12 g52 g64 g148) /\
      rw_cells psegs M1 (sa + 5888) [CB 8 j3a; C4 (Z_to_bv 64 16384); CB 52 j3b; C8 (Z_to_bv 64 0); CB 8 j3c] /\
      ms' = MS (mkR (Z_to_bv 64 0x16620) (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7
                    (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 65536) (Z_to_bv 64 16384) (Z_to_bv 64 4) (Z_to_bv 64 0x1a9f4) x14 x15 x16 x17
                    (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs)).
  { unfold TFC in TD |- *.
    eapply (fl_seg_h usp _ n cp up sa wnd prv hd m F fc p0 p96 g12 g52 g64 g92a g104a g120 g148 j3 s3) with (x23 := Z_to_bv 64 15);
      [lia| lia| lia| lia| lia| lia| lia| lia| exact TD| exact SC| exact S3| exact (md_mi _ _ _ _ H)|].
    intros M1 g128 j3a j3b j3c MU WM MI1 TD' SC' S3'x. exists M1, g128, j3a, j3b, j3c. unfold SCH. cbn [app].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact TD'|]. split; [exact SC'|]. split; [exact S3'x| reflexivity]. }
  intros ms' (M1 & g128 & j3a & j3b & j3c & MU & WM & MI1 & TD1 & SC1 & S31 & ->).
  assert (H1 : MID [(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s M1).
  { apply (MID_munch _ _ s m M1 _ H MU WM MI1).
    repeat (apply Forall_cons; [right; exists (ps, sa, 5968); split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|]). apply Forall_nil. }
  pose proof (same_on_munch _ _ _ MU WM) as SO1.
  assert (OUTk : forall x, ((x < sa \/ sa + 5968 <= x) \/ in_szero sa x) -> outside [(sa + 120, sa + 128); (sa + 5896, sa + 5900); (sa + 5952, sa + 5960)] x)
    by (intros x Hx; unfold in_szero in Hx; cbn; lia).
  assert (Oh : forall x, hd <= x < hd + 65536 -> x < sa \/ sa + 5968 <= x).
  { pose proof (MID_apart _ _ _ _ 3 0 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (Op : forall x, prv <= x < prv + 65536 -> x < sa \/ sa + 5968 <= x).
  { pose proof (MID_apart _ _ _ _ 3 1 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (Ow : forall x, wnd <= x < wnd + 65536 -> x < sa \/ sa + 5968 <= x).
  { pose proof (MID_apart _ _ _ _ 3 2 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (OC : forall x, cp <= x < cp + cl0 -> x < sa \/ sa + 5968 <= x).
  { pose proof (MID_apart _ _ _ _ 3 5 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (DI1 : rw_cells psegs M1 (usp + -280) (DI2 cp)).
  { eapply rw_cells_magree; [exact SO1| exact DI|]. intros a Ha. apply OUTk. left. cbn in Ha. lia. }
  assert (ZS1 : szero M1 sa).
  { eapply szero_same_on; [exact SO1| lia| lia| | exact ZS]. intros x Hx. apply OUTk. right; exact Hx. }
  assert (Zw1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 wnd 65536) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (Ow x Hx)| lia| lia| lia| exact Zw]).
  assert (Zp1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 prv 65536) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (Op x Hx)| lia| lia| lia| exact Zp]).
  assert (Zh1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 hd 65536) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (Oh x Hx)| lia| lia| lia| exact Zh]).
  assert (Zcp1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 cp cl0) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (OC x Hx)| lia| lia| lia| exact Zcp]).
  clear SO1 OUTk Oh Op Ow OC TD DI SC S3 ZS Zw Zp Zh Zcp MU WM.
  destruct (md_err _ _ _ _ H1) as [errv ER].
  apply implM_bind_assoc. unfold HarnessC.DBLK_N.
  eapply implM_zreq.
  { unfold rmalloc_stmt_z in MALLOCZ.
    eapply MALLOCZ with (lo := lo) (B := AB) (LB := [(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)
                        (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -288)) by lia.
    - exact (md_heap _ _ _ _ H1).
    - exact (md_aux _ _ _ _ H1).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H1). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact MI1.
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros ppb s' ms' PO FRSH.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -288)) in ST' by lia. rewrite ?(unsigned_lit (usp + -288)) in HPR by lia.
  destruct RES as (A & junk & -> & BR & HEAP' & BLK & _ & ZJ). specialize (ZJ FRSH). subst junk.
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ 65536 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(ppb, A, 65536); (ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ _ _ cl0 s s' M1 m' (usp + -288) H1 HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  assert (IS : In (ps, sa, 5968) ([(ph, hd, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) by (do 3 right; left; reflexivity).
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_di s' m' ppb ph pv pw ps pc pu A hd prv wnd sa cp up p0 p96 g12 g52 g64 g92a g104a g128 g148 j3a j3b j3c); [exact H'| | | | | | | | | |].
  - eapply rw_cells_magree; [exact SO| exact TD1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact SO| exact DI1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact SC1].
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact S31].
  - exact (szero_heap _ _ M1 m' ps sa HPR IS ltac:(lia) ltac:(lia) ZS1).
  - exact (zblk_heap _ _ M1 m' pw wnd 65536 HPR ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zw1).
  - exact (zblk_heap _ _ M1 m' pv prv 65536 HPR ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zp1).
  - exact (zblk_heap _ _ M1 m' ph hd 65536 HPR ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zh1).
  - apply (zeros_at_of_chunk m' A 65536 BLK). lia.
  - exact (zblk_heap _ _ M1 m' pc cp cl0 HPR ltac:(do 5 right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zcp1).
Qed.

Lemma L_p : forall s m (pv pw ps pc pu : bptr) (prv wnd sa cp up : Z)
    (p0 p96 g12 g52 g64 g92a g104 g148 j3 : list byte)
    (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pv, prv, FL_DBLK_N); (pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  rw_cells psegs m (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) ->
  rw_cells psegs m (usp + -280) (DI2 cp) ->
  rw_cells psegs m sa (SCH [CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 28 g104] g12 g52 g64 g148) ->
  rw_cells psegs m (sa + 5888) [CB 80 j3] ->
  szero m sa ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m wnd FL_DBLK_N -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m prv FL_DBLK_N ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (mbind (hd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;; pb <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;;
                      (raw_free pb ;;; raw_free hd ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT)) (KTS pc pu)) s POST
    (MS (mkR (Z_to_bv 64 0x165e0) (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 prv) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x165e0) fc None m (seg_rom psegs)).
Proof.
  intros s m pv pw ps pc pu prv wnd sa cp up p0 p96 g12 g52 g64 g92a g104 g148 j3
         x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TD DI SC S3 ZS Zw Zp Zcp.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CBR. pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ _ (pv, prv, FL_DBLK_N) H ltac:(left; reflexivity)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(right; left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(do 2 right; left; reflexivity)) as (S1 & S2 & S3' & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 3 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 4 right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5).
  cbn [blk_addr blk_size fst snd] in V1, V2, V3, V4, V5, W1, W2, W3, W4, W5, S1, S2, S3', S4, S5, Q1, Q2, Q3, Q4, Q5, R1, R2, R3, R4, R5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  unfold SCH in SC. cbn [app] in SC.
  eapply implM_evt with (P := fun ms' => exists (M1 : mem) (g104a g120 : list byte),
      munch [(sa + 112, sa + 120)] m M1 /\ wmono psegs m M1 /\ mem_inv psegs M1 /\
      rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) /\
      rw_cells psegs M1 sa (SCH [CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 8 g104a; C8 (Z_to_bv 64 prv); CB 12 g120] g12 g52 g64 g148) /\
      ms' = MS (mkR (Z_to_bv 64 0x165fc) (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7
                    (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 65536) (Z_to_bv 64 32768) (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 0x1a9f4) x15 x16 x17
                    (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs)).
  { unfold TFC in TD |- *.
    eapply (fl_seg_p usp _ n cp up sa wnd prv m F fc p0 p96 g12 g52 g64 g92a g104 g148 s3) with (x23 := Z_to_bv 64 15);
      [lia| lia| lia| lia| lia| lia| lia| exact TD| exact SC| exact (md_mi _ _ _ _ H)|].
    intros M1 g104a g120 MU WM MI1 TD' SC'. exists M1, g104a, g120. unfold SCH. cbn [app].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact TD'|]. split; [exact SC'| reflexivity]. }
  intros ms' (M1 & g104a & g120 & MU & WM & MI1 & TD1 & SC1 & ->).
  assert (H1 : MID [(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s M1).
  { apply (MID_munch _ _ s m M1 _ H MU WM MI1).
    apply Forall_cons; [right; exists (ps, sa, 5968); split; [do 2 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| apply Forall_nil]. }
  pose proof (same_on_munch _ _ _ MU WM) as SO1.
  assert (OUTk : forall x, ((x < sa + 112 \/ sa + 120 <= x) \/ in_szero sa x) -> outside [(sa + 112, sa + 120)] x)
    by (intros x Hx; unfold in_szero in Hx; cbn; lia).
  assert (Op : forall x, prv <= x < prv + 65536 -> x < sa + 112 \/ sa + 120 <= x).
  { pose proof (MID_apart _ _ _ _ 2 0 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (Ow : forall x, wnd <= x < wnd + 65536 -> x < sa + 112 \/ sa + 120 <= x).
  { pose proof (MID_apart _ _ _ _ 2 1 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (OC : forall x, cp <= x < cp + cl0 -> x < sa + 112 \/ sa + 120 <= x).
  { pose proof (MID_apart _ _ _ _ 2 4 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (DI1 : rw_cells psegs M1 (usp + -280) (DI2 cp)).
  { eapply rw_cells_magree; [exact SO1| exact DI|]. intros a Ha. apply OUTk. left. cbn in Ha. lia. }
  assert (S31 : rw_cells psegs M1 (sa + 5888) [CB 80 j3]).
  { eapply rw_cells_magree; [exact SO1| exact S3|]. intros a Ha. apply OUTk. left. cbn in Ha. lia. }
  assert (ZS1 : szero M1 sa).
  { eapply szero_same_on; [exact SO1| lia| lia| | exact ZS]. intros x Hx. apply OUTk. right; exact Hx. }
  assert (Zw1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 wnd 65536) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (Ow x Hx)| lia| lia| lia| exact Zw]).
  assert (Zp1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 prv 65536) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (Op x Hx)| lia| lia| lia| exact Zp]).
  assert (Zcp1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 cp cl0) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (OC x Hx)| lia| lia| lia| exact Zcp]).
  clear SO1 OUTk Op Ow OC TD DI SC S3 ZS Zw Zp Zcp MU WM.
  destruct (md_err _ _ _ _ H1) as [errv ER].
  apply implM_bind_assoc. unfold HarnessC.DBLK_N.
  eapply implM_zreq.
  { unfold rmalloc_stmt_z in MALLOCZ.
    eapply MALLOCZ with (lo := lo) (B := AB) (LB := [(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)
                        (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -288)) by lia.
    - exact (md_heap _ _ _ _ H1).
    - exact (md_aux _ _ _ _ H1).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H1). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact MI1.
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros ph s' ms' PO FRSH.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -288)) in ST' by lia. rewrite ?(unsigned_lit (usp + -288)) in HPR by lia.
  destruct RES as (A & junk & -> & BR & HEAP' & BLK & _ & ZJ). specialize (ZJ FRSH). subst junk.
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ 65536 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(ph, A, 65536); (pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ _ _ cl0 s s' M1 m' (usp + -288) H1 HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  assert (IS : In (ps, sa, 5968) ([(pv, prv, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) by (do 2 right; left; reflexivity).
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_h s' m' ph pv pw ps pc pu A prv wnd sa cp up p0 p96 g12 g52 g64 g92a g104a g120 g148 j3); [exact H'| | | | | | | | |].
  - eapply rw_cells_magree; [exact SO| exact TD1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact SO| exact DI1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact SC1].
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact S31].
  - exact (szero_heap _ _ M1 m' ps sa HPR IS ltac:(lia) ltac:(lia) ZS1).
  - exact (zblk_heap _ _ M1 m' pw wnd 65536 HPR ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zw1).
  - exact (zblk_heap _ _ M1 m' pv prv 65536 HPR ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zp1).
  - apply (zeros_at_of_chunk m' A 65536 BLK). lia.
  - exact (zblk_heap _ _ M1 m' pc cp cl0 HPR ltac:(do 4 right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zcp1).
Qed.

Lemma L_w : forall s m (pw ps pc pu : bptr) (wnd sa cp up : Z)
    (p0 p96 g12 g52 g64 g92 g148 j3 : list byte)
    (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pw, wnd, FL_DBLK_N); (ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  rw_cells psegs m (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) ->
  rw_cells psegs m (usp + -280) (DI2 cp) ->
  rw_cells psegs m sa (SCH [CB 40 g92] g12 g52 g64 g148) ->
  rw_cells psegs m (sa + 5888) [CB 80 j3] ->
  szero m sa ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m wnd FL_DBLK_N ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (mbind (pv <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;; hd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;;
                      pb <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;;
                      (raw_free pb ;;; raw_free hd ;;; raw_free pv ;;; raw_free pw ;;; raw_free ps ;;; TFT)) (KTS pc pu)) s POST
    (MS (mkR (Z_to_bv 64 0x165c4) (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 wnd) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x165c4) fc None m (seg_rom psegs)).
Proof.
  intros s m pw ps pc pu wnd sa cp up p0 p96 g12 g52 g64 g92 g148 j3
         x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TD DI SC S3 ZS Zw Zcp.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CBR. pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ _ (pw, wnd, FL_DBLK_N) H ltac:(left; reflexivity)) as (W1 & W2 & W3 & W4 & W5).
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(right; left; reflexivity)) as (S1 & S2 & S3' & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(do 2 right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 3 right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5).
  cbn [blk_addr blk_size fst snd] in W1, W2, W3, W4, W5, S1, S2, S3', S4, S5, Q1, Q2, Q3, Q4, Q5, R1, R2, R3, R4, R5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  unfold SCH in SC. cbn [app] in SC.
  eapply implM_evt with (P := fun ms' => exists (M1 : mem) (g92a g104 : list byte),
      munch [(sa + 96, sa + 104)] m M1 /\ wmono psegs m M1 /\ mem_inv psegs M1 /\
      rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) /\
      rw_cells psegs M1 sa (SCH [CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 28 g104] g12 g52 g64 g148) /\
      ms' = MS (mkR (Z_to_bv 64 0x165e0) (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7
                    (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 65536) (Z_to_bv 64 32768) (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 0x1a9f4) x15 x16 x17
                    (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs)).
  { unfold TFC in TD |- *.
    eapply (fl_seg_w usp _ n cp up sa wnd m F fc p0 p96 g12 g52 g64 g92 g148 s3) with (x23 := Z_to_bv 64 15);
      [lia| lia| lia| lia| lia| lia| exact TD| exact SC| exact (md_mi _ _ _ _ H)|].
    intros M1 g92a g104 MU WM MI1 TD' SC'. exists M1, g92a, g104. unfold SCH. cbn [app].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact TD'|]. split; [exact SC'| reflexivity]. }
  intros ms' (M1 & g92a & g104 & MU & WM & MI1 & TD1 & SC1 & ->).
  assert (H1 : MID [(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s M1).
  { apply (MID_munch _ _ s m M1 _ H MU WM MI1).
    apply Forall_cons; [right; exists (ps, sa, 5968); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| apply Forall_nil]. }
  pose proof (same_on_munch _ _ _ MU WM) as SO1.
  assert (OUTk : forall x, ((x < sa + 96 \/ sa + 104 <= x) \/ in_szero sa x) -> outside [(sa + 96, sa + 104)] x)
    by (intros x Hx; unfold in_szero in Hx; cbn; lia).
  assert (Ow : forall x, wnd <= x < wnd + 65536 -> x < sa + 96 \/ sa + 104 <= x).
  { pose proof (MID_apart _ _ _ _ 1 0 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (OC : forall x, cp <= x < cp + cl0 -> x < sa + 96 \/ sa + 104 <= x).
  { pose proof (MID_apart _ _ _ _ 1 3 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx. lia. }
  assert (DI1 : rw_cells psegs M1 (usp + -280) (DI2 cp)).
  { eapply rw_cells_magree; [exact SO1| exact DI|]. intros a Ha. apply OUTk. left. cbn in Ha. lia. }
  assert (S31 : rw_cells psegs M1 (sa + 5888) [CB 80 j3]).
  { eapply rw_cells_magree; [exact SO1| exact S3|]. intros a Ha. apply OUTk. left. cbn in Ha. lia. }
  assert (ZS1 : szero M1 sa).
  { eapply szero_same_on; [exact SO1| lia| lia| | exact ZS]. intros x Hx. apply OUTk. right; exact Hx. }
  assert (Zw1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 wnd 65536) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (Ow x Hx)| lia| lia| lia| exact Zw]).
  assert (Zcp1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 cp cl0) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (OC x Hx)| lia| lia| lia| exact Zcp]).
  clear SO1 OUTk Ow OC TD DI SC S3 ZS Zw Zcp MU WM.
  destruct (md_err _ _ _ _ H1) as [errv ER].
  apply implM_bind_assoc. unfold HarnessC.DBLK_N.
  eapply implM_zreq.
  { unfold rmalloc_stmt_z in MALLOCZ.
    eapply MALLOCZ with (lo := lo) (B := AB) (LB := [(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)
                        (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -288)) by lia.
    - exact (md_heap _ _ _ _ H1).
    - exact (md_aux _ _ _ _ H1).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H1). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact MI1.
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros pv s' ms' PO FRSH.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -288)) in ST' by lia. rewrite ?(unsigned_lit (usp + -288)) in HPR by lia.
  destruct RES as (A & junk & -> & BR & HEAP' & BLK & _ & ZJ). specialize (ZJ FRSH). subst junk.
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ 65536 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(pv, A, 65536); (pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ _ _ cl0 s s' M1 m' (usp + -288) H1 HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  assert (IS : In (ps, sa, 5968) ([(pw, wnd, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) by (right; left; reflexivity).
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_p s' m' pv pw ps pc pu A wnd sa cp up p0 p96 g12 g52 g64 g92a g104 g148 j3); [exact H'| | | | | | | |].
  - eapply rw_cells_magree; [exact SO| exact TD1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact SO| exact DI1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact SC1].
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact S31].
  - exact (szero_heap _ _ M1 m' ps sa HPR IS ltac:(lia) ltac:(lia) ZS1).
  - exact (zblk_heap _ _ M1 m' pw wnd 65536 HPR ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zw1).
  - apply (zeros_at_of_chunk m' A 65536 BLK). lia.
  - exact (zblk_heap _ _ M1 m' pc cp cl0 HPR ltac:(do 3 right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zcp1).
Qed.

Lemma L_s : forall s m (ps pc pu : bptr) (sa cp up : Z) (p0 p64 p96 : list byte)
    (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(ps, sa, FL_DSTATE_N); (pu, up, n); (pc, cp, cl0)] cl0 s m ->
  rw_cells psegs m (usp + -208) (TFC p0 (CB 8 p64) p96 s3 up cp n) ->
  rw_cells psegs m (usp + -280) (DI2 cp) ->
  rw_cells psegs m sa [CB (Z.to_nat 5968) (repeat (Z_to_bv 8 0) (Z.to_nat 5968))] ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (mbind (w <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;; pv <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;;
                      hd <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;; pb <- HarnessC.zreq raw_malloc fresh_topb HarnessC.DBLK_N ;;
                      (raw_free pb ;;; raw_free hd ;;; raw_free pv ;;; raw_free w ;;; raw_free ps ;;; TFT)) (KTS pc pu)) s POST
    (MS (mkR (Z_to_bv 64 0x16524) (Z_to_bv 64 (usp + -288)) gp tp x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 cp) (Z_to_bv 64 sa) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 5968) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16524) fc None m (seg_rom psegs)).
Proof.
  intros s m ps pc pu sa cp up p0 p64 p96 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H TD DI BS Zcp.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CBR. pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ _ (ps, sa, FL_DSTATE_N) H ltac:(left; reflexivity)) as (S1 & S2 & S3' & S4 & S5).
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(do 2 right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5).
  cbn [blk_addr blk_size fst snd] in S1, S2, S3', S4, S5, Q1, Q2, Q3, Q4, Q5, R1, R2, R3, R4, R5.
  unfold FL_DSTATE_N, FL_DBLK_N in *.
  pose proof (szero_of_block m sa BS ltac:(lia) ltac:(lia)) as ZS.
  (* 1.4 UBSan: after fl_seg_s_ok's memset call t1, t2, a3, a4, t3-t6 are fresh (y6 y7 y13 y14 y28-y31); the memset
     rewrote zeros over the zalloc'd zeros, so the munch names only the stored fields *)
  eapply implM_evt with (P := fun ms' => exists (M1 : mem) (g12 g52 g64 g92 g148 j2 j3 : list byte) (y6 y7 y13 y14 y28 y29 y30 y31 : word),
      munch [(usp + -144, usp + -136); (sa, sa + 12); (sa + 48, sa + 52); (sa + 56, sa + 64); (sa + 80, sa + 92); (sa + 132, sa + 148)] m M1 /\
      wmono psegs m M1 /\ mem_inv psegs M1 /\
      rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 sa)) p96 s3 up cp n) /\
      rw_cells psegs M1 sa (SCH [CB 40 g92] g12 g52 g64 g148) /\
      rw_cells psegs M1 (sa + 5888) [CB (Z.to_nat 80) j3] /\
      ms' = MS (mkR (Z_to_bv 64 0x165c4) (Z_to_bv 64 (usp + -288)) gp tp (Z_to_bv 64 32767) y6 y7
                    (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 sa) (Z_to_bv 64 65536) (Z_to_bv 64 32768) (Z_to_bv 64 2) y13 y14
                    (Z_to_bv 64 42) (Z_to_bv 64 0x1a9f4) (Z_to_bv 64 2907)
                    (Z_to_bv 64 (sa + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 y28 y29 y30 y31)
               F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs)).
  { unfold TFC in TD |- *.
    eapply (fl_seg_s_ok usp ltac:(lia) SP16 _ n cp up sa m F fc p0 p64 p96);
      [lia| lia| lia| lia| lia| lia| exact S2| exact TD| exact BS| exact (md_mi _ _ _ _ H)|].
    intros M1 g12 g52 g64 g92 g148 j2 j3 y6 y7 y13 y14 y28 y29 y30 y31 MU WM MI1 TD' SC' S2' S3x.
    exists M1, g12, g52, g64, g92, g148, j2, j3, y6, y7, y13, y14, y28, y29, y30, y31. unfold SCH. cbn [app].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact TD'|]. split; [exact SC'|]. split; [exact S3x| reflexivity]. }
  intros ms' (M1 & g12 & g52 & g64 & g92 & g148 & j2 & j3 & y6 & y7 & y13 & y14 & y28 & y29 & y30 & y31 & MU & WM & MI1 & TD1 & SC1 & S31 & ->).
  assert (H1 : MID [(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s M1).
  { apply (MID_munch _ _ s m M1 _ H MU WM MI1).
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    repeat (apply Forall_cons; [right; exists (ps, sa, 5968); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|]). apply Forall_nil. }
  pose proof (same_on_munch _ _ _ MU WM) as SO1.
  assert (OUTk : forall x, (((x < sa \/ sa + 5968 <= x) /\ (x < usp - 144 \/ usp - 136 <= x)) \/ in_szero sa x) ->
                 outside [(usp + -144, usp + -136); (sa, sa + 12); (sa + 48, sa + 52); (sa + 56, sa + 64); (sa + 80, sa + 92); (sa + 132, sa + 148)] x).
  { intros x Hx. unfold in_szero in Hx. cbn. clear -Hx S4 U2 U3. lia. }
  assert (OC : forall x, cp <= x < cp + cl0 -> (x < sa \/ sa + 5968 <= x) /\ (x < usp - 144 \/ usp - 136 <= x)).
  { pose proof (MID_apart _ _ _ _ 0 2 _ _ H eq_refl eq_refl ltac:(discriminate)) as A. cbn [blk_addr blk_size fst snd] in A. unfold OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.apart in A. intros x Hx. clear -A Hx R4 U2 U3. lia. }
  assert (DI1 : rw_cells psegs M1 (usp + -280) (DI2 cp)).
  { eapply rw_cells_magree; [exact SO1| exact DI|]. intros a Ha. apply OUTk. left. cbn in Ha. lia. }
  assert (ZS1 : szero M1 sa).
  { eapply szero_same_on; [exact SO1| lia| lia| | exact ZS]. intros x Hx. apply OUTk. right; exact Hx. }
  assert (Zcp1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 cp cl0) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; apply OUTk; left; exact (OC x Hx)| lia| lia| lia| exact Zcp]).
  clear SO1 OUTk OC TD DI BS ZS Zcp MU WM.
  destruct (md_err _ _ _ _ H1) as [errv ER].
  apply implM_bind_assoc. unfold HarnessC.DBLK_N.
  eapply implM_zreq.
  { unfold rmalloc_stmt_z in MALLOCZ.
    eapply MALLOCZ with (lo := lo) (B := AB) (LB := [(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB) (n := 65536) (errv := errv);
      rewrite ?(unsigned_lit (usp + -288)) by lia.
    - exact (md_heap _ _ _ _ H1).
    - exact (md_aux _ _ _ _ H1).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H1). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact MI1.
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros pw s' ms' PO FRSH.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -288)) in ST' by lia. rewrite ?(unsigned_lit (usp + -288)) in HPR by lia.
  destruct RES as (A & junk & -> & BR & HEAP' & BLK & _ & ZJ). specialize (ZJ FRSH). subst junk.
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ 65536 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(pw, A, 65536); (ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ _ _ cl0 s s' M1 m' (usp + -288) H1 HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  assert (IS : In (ps, sa, 5968) ([(ps, sa, 5968); (pu, up, n); (pc, cp, cl0)] ++ LB)) by (left; reflexivity).
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_w s' m' pw ps pc pu A sa cp up p0 p96 g12 g52 g64 g92 g148 j3); [exact H'| | | | | | |].
  - eapply rw_cells_magree; [exact SO| exact TD1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact SO| exact DI1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact SC1].
  - eapply (schunk_heap _ _ M1 m' ps sa); [exact HPR| exact IS| lia| cbn; lia| exact S31].
  - exact (szero_heap _ _ M1 m' ps sa HPR IS ltac:(lia) ltac:(lia) ZS1).
  - apply (zeros_at_of_chunk m' A 65536 BLK). lia.
  - exact (zblk_heap _ _ M1 m' pc cp cl0 HPR ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zcp1).
Qed.

Lemma L_tf1 : forall s m (pc pu : bptr) (cp up : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pu, up, n); (pc, cp, cl0)] cl0 s m ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (mbind (HarnessC.test_flush_m FLM raw_malloc raw_free fresh_topb payload n) (KTS pc pu)) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 up) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 cp) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16344) fc None m (seg_rom psegs)).
Proof.
  intros s m pc pu cp up x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H Zcp.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CBR. pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ _ (pu, up, n) H ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5).
  cbn [blk_addr blk_size fst snd] in Q1, Q2, Q3, Q4, Q5, R1, R2, R3, R4, R5.
  pose proof (md_st _ _ _ _ H) as STAT. unfold HDATA in STAT.
  eapply implM_evt with (P := fun ms' => exists (M1 : mem) (p0 p64 p96 : list byte),
      munch [(usp + -288, usp + -48)] m M1 /\ wmono psegs m M1 /\ mem_inv psegs M1 /\
      rw_cells psegs M1 (usp + -208) (TFC p0 (CB 8 p64) p96 s3 up cp n) /\ rw_cells psegs M1 (usp + -280) (DI2 cp) /\
      ms' = MS (mkR (Z_to_bv 64 0x16524) (Z_to_bv 64 (usp + -288)) gp tp (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 (-8)) x7
                    (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 cp) (Z_to_bv 64 5968) (Z_to_bv 64 1) (Z_to_bv 64 5968) (Z_to_bv 64 15) (Z_to_bv 64 8)
                    (Z_to_bv 64 0) (Z_to_bv 64 0x1a9f4) (Z_to_bv 64 0)
                    (Z_to_bv 64 5968) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs)).
  { eapply (fl_seg_tf1 usp ltac:(lia) SP16 _ D n cp up lo m F fc); [lia| lia| exact NR| lia| lia| lia| apply (MID_stk_below _ _ _ _ _ H); lia| exact (md_mi _ _ _ _ H)
      | apply relro_of_hc; exact (md_hc _ _ _ _ H)| exact STAT|].
    (* 1.4 UBSan: the frame's first 8 bytes (usp - 288) are padding q0; DI2 starts at usp - 280 *)
    intros M1 p0 p64 p96 q0 MU WM MI1 ST1 TD DI ST'. exists M1, p0, p64, p96.
    pose proof (rw_cells_app_split M1 (usp + -288) [CB 8 q0] (DI2 cp) DI) as [_ DI'].
    change (Z.of_nat (cells_size [CB 8 q0])) with 8 in DI'. replace (usp + -288 + 8) with (usp + -280) in DI' by lia.
    unfold TFC.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact TD|]. split; [exact DI'| reflexivity]. }
  intros ms' (M1 & p0 & p64 & p96 & MU & WM & MI1 & TD1 & DI1 & ->).
  assert (H1 : MID [(pu, up, n); (pc, cp, cl0)] cl0 s M1).
  { apply (MID_munch _ _ s m M1 _ H MU WM MI1). apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
  pose proof (same_on_munch _ _ _ MU WM) as SO1.
  assert (Zcp1 : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs M1 cp cl0) by (eapply zeros_at_same_on; [exact SO1| intros x Hx; cbn; lia| lia| lia| lia| exact Zcp]).
  clear SO1 Zcp MU WM.
  destruct (md_err _ _ _ _ H1) as [errv ER].
  unfold HarnessC.test_flush_m. apply implM_bind_assoc. unfold HarnessC.DSTATE_N.
  eapply implM_zreq.
  { unfold rmalloc_stmt_z in MALLOCZ.
    eapply MALLOCZ with (lo := lo) (B := AB) (LB := [(pu, up, n); (pc, cp, cl0)] ++ LB) (n := 5968) (errv := errv);
      rewrite ?(unsigned_lit (usp + -288)) by lia.
    - exact (md_heap _ _ _ _ H1).
    - exact (md_aux _ _ _ _ H1).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H1). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact MI1.
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros ps s' ms' PO FRSH.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -288)) in ST' by lia. rewrite ?(unsigned_lit (usp + -288)) in HPR by lia.
  destruct RES as (A & junk & -> & BR & HEAP' & BLK & _ & ZJ). specialize (ZJ FRSH). subst junk.
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ 5968 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(ps, A, 5968); (pu, up, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ _ _ cl0 s s' M1 m' (usp + -288) H1 HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (same_on_rheap_pres _ _ _ _ HPR) as SO.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_s s' m' ps pc pu A cp up p0 p64 p96); [exact H'| | | exact BLK|].
  - eapply rw_cells_magree; [exact SO| exact TD1|]. intros a Ha. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact SO| exact DI1|]. intros a Ha. left. cbn in Ha. lia.
  - exact (zblk_heap _ _ M1 m' pc cp cl0 HPR ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zcp1).
Qed.

Lemma L_c1 : forall s m (pc : bptr) (cp : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [(pc, cp, cl0)] cl0 s m -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m cp cl0 ->
  implM psegs (up <- HarnessC.creq raw_malloc n ;;
               (clen' <- HarnessC.test_flush_m FLM raw_malloc raw_free fresh_topb payload n ;;
                (HarnessC.test_sync_m FLM raw_malloc raw_free fresh_topb cmp clen' n ;;; REST pc up))) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 cp) x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16334) fc None m (seg_rom psegs)).
Proof.
  intros s m pc cp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H Zcp.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. pose proof cl_range as CBR. pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ _ (pc, cp, cl0) H ltac:(left; reflexivity)) as (R1 & R2 & R3 & R4 & R5).
  cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5.
  destruct (md_err _ _ _ _ H) as [errv ER].
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply (fl_seg_c1 usp _ n cp); [lia| lia| reflexivity]| intros ms' ->].
  eapply implM_creq.
  { unfold rcalloc_stmt in CALLOC.
    eapply CALLOC with (lo := lo) (B := AB) (LB := [(pc, cp, cl0)] ++ LB) (n := n) (errv := errv);
      rewrite ?(unsigned_lit (usp + -48)) by lia.
    - exact (md_heap _ _ _ _ H).
    - exact (md_aux _ _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RCALLOC_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ _ H).
    - exact TP.
    - reflexivity.
    - reflexivity.
    - lia. }
  cbv beta. intros pu s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp + -48)) in ST' by lia. rewrite ?(unsigned_lit (usp + -48)) in HPR by lia.
  destruct RES as (A & -> & BR & HEAP' & BLK & _).
  destruct BR as (A1 & A2 & A3 & A4 & A5).
  pose proof (rw_cells_wr_at _ _ _ _ n BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
  assert (H' : MID [(pu, A, n); (pc, cp, cl0)] cl0 s' m').
  { apply (MID_heap _ _ _ cl0 s s' m m' (usp + -48) H HPR);
      [intros b Hb; apply in_or_app; right; exact Hb
      | intros b [<-|Hb]; [right; exact WRA| left; split; [exact Hb| apply in_or_app; left; exact Hb]]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply (L_tf1 s' m' pc pu cp A); [exact H'| exact (zblk_heap _ _ m m' pc cp cl0 HPR ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Zcp)].
Qed.
End RUN.

Lemma MID_entry : forall (M1 : mem) (errv : word) (pad : list byte),
  4 <= n <= 2^20 ->
  RHEAP st0 LB m0 -> bytes_at psegs m0 D pbytes -> wr_at psegs m0 D n -> harness_cells m0 -> stderr_wfile0 m0 ->
  rauxv_ok m0 AB -> stk psegs m0 lo usp -> rw_cells psegs m0 (errno_addr tp) [C4 errv] -> mem_inv psegs m0 ->
  munch [(usp + -48, usp); (0x3d6a0, 0x3d6b0)] m0 M1 -> wmono psegs m0 M1 -> mem_inv psegs M1 ->
  rw_cells psegs M1 (usp + -48) (HF pad cl0) -> rw_cells psegs M1 0x3d6a0 [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 D)] ->
  MID [] cl0 st0 M1.
Proof.
  intros M1 errv pad N1 HEAP BY WR HC SF AUX ST ER MI MU WM MI1 HFc STc.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  assert (BLK : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. exact (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b HEAP Hb). }
  assert (OUT : forall x, (usp <= x \/ x < usp - 48) -> ~ (0x3d6a0 <= x < 0x3d6b0) -> outside [(usp + -48, usp); (0x3d6a0, 0x3d6b0)] x).
  { intros x Hx Hy. cbn [outside fst snd]. split; [lia|]. split; [lia| exact I]. }
  constructor.
  - cbn [app]. eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|].
    apply Forall_cons; [left; cbn [fst]; lia|]. apply Forall_cons; [| apply Forall_nil].
    right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
  - exact MI1.
  - eapply stk_wmono; [exact ST| lia| exact WM].
  - exists errv. eapply rw_cells_magree; [exact SO| exact ER|].
    intros a Ha. rewrite TP in Ha. unfold wz, RATP in Ha. rewrite unsigned_lit in Ha by lia.
    change (Z.of_nat (cells_size [C4 errv])) with 4 in Ha. unfold RERRNO in Ha. apply OUT; lia.
  - eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; split; [lia| right; lia]|].
    apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; split; [lia| left; lia]| apply Forall_nil].
  - intros a Ha Hc NB. apply SO; [exact Ha|]. unfold hown_addr, HDATA, HDATA_N in NB. apply OUT; [| lia].
    destruct Hc as [Hc|[[Hc NS]|(b & Hb & Hr)]]; [left; exact Hc| right; lia|].
    pose proof (BLK b Hb) as (_ & _ & _ & B4 & _). right. lia.
  - reflexivity.
  - intros a Ha. destruct (SO a ltac:(unfold PRELRO_LO, PRELRO_HI in Ha; lia) ltac:(apply OUT; unfold PRELRO_LO, PRELRO_HI in Ha; lia)) as [E _].
    unfold wa in E. rewrite E. exact (HC a Ha).
  - destruct SF as (flags & mode & e & wend & tail & FC & FL & WE & HE). exists flags, mode, e, wend, tail.
    split; [| split; [exact FL| split; [exact WE| exact HE]]].
    eapply rw_cells_magree; [exact SO| exact FC|]. intros a Ha. rewrite file_cells_size in Ha. apply OUT; lia.
  - exists pad. replace (usp - 48) with (usp + -48) by lia. exact HFc.
  - pose proof (CLEN_ge n ltac:(lia)). pose proof (CLEN_lt32 n ltac:(lia)). lia.
  - exact STc.
  - eapply pay_same_on; [exact SO| | exact BY]. intros b a Hb Ha. pose proof (BLK b Hb) as (_ & _ & _ & B4 & B5). apply OUT; lia.
  - eapply pwr_same_on; [exact SO| | exact WR]. intros b a Hb Ha. pose proof (BLK b Hb) as (_ & _ & _ & B4 & B5). apply OUT; lia.
  - apply Forall_nil.
Qed.

Theorem fuzz_one_call : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word),
  (4 <= n <= 2^20 -> forall fx, fl_links (FLIB fx) FLM WB payload) ->
  RHEAP st0 LB m0 -> bytes_at psegs m0 D pbytes -> wr_at psegs m0 D n -> harness_cells m0 -> stderr_wfile0 m0 ->
  rauxv_ok m0 AB -> stk psegs m0 lo usp -> rw_cells psegs m0 (errno_addr tp) [C4 errv] -> mem_inv psegs m0 ->
  implMC psegs (ProgC.fuzz_oneC FLM payload) st0 POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PFUZZ_ENTRY) fc None m0 (seg_rom psegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv LINKS HEAP BY WR HC SF AUX ST ER MI.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof n_nonneg as N0. unfold HARNESS_STACK in LO.
  assert (BLK : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. exact (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b HEAP Hb). }
  rewrite (ProgC.fuzz_oneC_eq FLM). apply implMC_lift. unfold ProgC.fuzz_oneM, HarnessC.fuzz_one_m. cbv zeta.
  unfold wz, PFUZZ_ENTRY. set (PO := POST). rewrite <- (Z_to_bv_bv_unsigned sp). subst PO.
  destruct (HarnessC.fuzz_skip n) eqn:SK.
  -
    assert (NR : 0 <= n <= 3 \/ 2^20 < n < 2^64).
    { unfold HarnessC.fuzz_skip, HarnessC.KMAX in SK. apply orb_prop in SK. destruct SK as [SK|SK]; [apply Z.leb_le in SK; left; lia| apply Z.ltb_lt in SK; right; lia]. }
    apply implM_ret.
    eapply (fl_seg_reject usp U1 _ D n lo m0 F fc); [lia| lia| exact NR| lia| exact ST| exact MI|].
    intros M1 y11 y12 y13 MU WM MI1 ST1.
    pose proof (same_on_munch _ _ _ MU WM) as SO.
    assert (OUT : forall x, (usp <= x \/ x < usp - 48) -> outside [(usp + -48, usp)] x) by (intros x Hx; cbn [outside fst snd]; split; [lia| exact I]).
    unfold fuzz_one_post. exists t0, t1, t2, y11, y12, y13, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, M1, errv, [].
    rewrite (Z_to_bv_bv_unsigned sp). split; [reflexivity|]. split; [lia|]. split; [exact MI1|]. split; [exact FRM|]. split; [exact ST1|].
    split. { eapply rw_cells_magree; [exact SO| exact ER|]. intros a Ha. rewrite TP in Ha. unfold wz, RATP in Ha. rewrite unsigned_lit in Ha by lia.
             change (Z.of_nat (cells_size [C4 errv])) with 4 in Ha. unfold RERRNO in Ha. apply OUT; lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; split; [lia| right; lia]| apply Forall_nil]. }
    split. { intros a Ha Hc NB. apply SO; [exact Ha|]. apply OUT.
             destruct Hc as [Hc|[[Hc NS]|(b & Hb & Hr)]]; [left; exact Hc| right; lia|]. pose proof (BLK b Hb) as (_ & _ & _ & B4 & _). right. lia. }
    split. { cbn [app]. eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|]. apply Forall_cons; [left; cbn [fst]; lia| apply Forall_nil]. }
    split; [split; [cbn; lia| apply Forall_nil]|].
    split. { intros a Ha. destruct (SO a ltac:(unfold PRELRO_LO, PRELRO_HI in Ha; lia) ltac:(apply OUT; unfold PRELRO_LO, PRELRO_HI in Ha; lia)) as [E _].
             unfold wa in E. rewrite E. exact (HC a Ha). }
    split. { destruct SF as (flags & mode & e & wend & tail & FC & FL & WE & HE). exists flags, mode, e, wend, tail.
             split; [| split; [exact FL| split; [exact WE| exact HE]]].
             eapply rw_cells_magree; [exact SO| exact FC|]. intros a Ha. rewrite file_cells_size in Ha. apply OUT; lia. }
    reflexivity.
  -
    assert (NR : 4 <= n <= 2^20).
    { unfold HarnessC.fuzz_skip, HarnessC.KMAX in SK. apply orb_false_iff in SK. destruct SK as [SK1 SK2]. apply Z.leb_gt in SK1. apply Z.ltb_ge in SK2. lia. }
    destruct (statics_chunk m0) as [old STAT0].
    eapply implM_evt with (P := fun ms' => exists (M1 : mem) (y12 y13 : word) (pad : list byte),
        munch [(usp + -48, usp); (0x3d6a0, 0x3d6b0)] m0 M1 /\ wmono psegs m0 M1 /\ mem_inv psegs M1 /\ stk psegs M1 lo (usp + -48) /\
        rw_cells psegs M1 (usp + -48) (HF pad cl0) /\ rw_cells psegs M1 0x3d6a0 [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 D)] /\
        ms' = MS (mkR (Z_to_bv 64 0x16334) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 D)
                      (Z_to_bv 64 1) (Z_to_bv 64 cl0) y12 y13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x23844) fc None M1 (seg_rom psegs)).
    { eapply (fl_seg_entry usp U1 _ D n lo m0 F fc old); [lia| lia| exact NR| lia| exact ST| exact MI| exact STAT0|].
      intros M1 y12 y13 pad MU WM MI1 ST1 HFc STc. exists M1, y12, y13, pad. rewrite cl_eq in HFc.
      split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact HFc|]. split; [exact STc| reflexivity]. }
    intros ms' (M1 & y12 & y13 & pad & MU & WM & MI1 & ST1 & HFc & STc & ->).
    pose proof (MID_entry M1 errv pad NR HEAP BY WR HC SF AUX ST ER MI MU WM MI1 HFc STc) as H1.
    destruct (md_err _ _ _ _ H1) as [errv1 ER1].
    pose proof (cl_range NR) as CBR.
    eapply implM_creq.
    { unfold rcalloc_stmt in CALLOC.
      eapply CALLOC with (lo := lo) (B := AB) (LB := [] ++ LB) (n := cl0) (errv := errv1);
        rewrite ?(unsigned_lit (usp + -48)) by lia.
      - exact (md_heap _ _ _ _ H1).
      - exact (md_aux _ _ _ _ H1).
      - lia.
      - apply (MID_stk_below _ _ _ _ _ H1). lia.
      - exact CEIL.
      - unfold RCALLOC_STACK. lia.
      - exact ER1.
      - exact MI1.
      - exact TP.
      - reflexivity.
      - reflexivity.
      - lia. }
    cbv beta. intros pc s' ms' PO.
    destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
    rewrite ?(unsigned_lit (usp + -48)) in ST' by lia. rewrite ?(unsigned_lit (usp + -48)) in HPR by lia.
    destruct RES as (A & -> & BR & HEAP' & BLK' & _).
    destruct BR as (A1 & A2 & A3 & A4 & A5).
    pose proof (rw_cells_wr_at _ _ _ _ cl0 BLK' ltac:(cbn [cells_size csize]; lia)) as WRA.
    assert (H' : MID [(pc, A, cl0)] cl0 s' m').
    { apply (MID_heap [] _ LB cl0 st0 s' M1 m' (usp + -48) H1 HPR);
        [intros b Hb; exact Hb| intros b [<-|[]]; right; exact WRA
        | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
    rewrite ret_pc_even by (first [lia| reflexivity]).
    eapply (L_c1 NR (LINKS NR) s' m' pc A); [exact H'| apply (zeros_at_of_chunk m' A cl0 BLK'); lia].
Qed.

End CALL.

Theorem fuzz_one_bridge : forall (FLM : flush_model) (FLIB : forall fx : OP.FPState, @fl_lib fx) (WB : ZPG.blk),
  (forall fx d, 4 <= zlength d <= 2^20 -> Forall (fun c => 0 <= c < 256) d -> fl_links (FLIB fx) FLM WB d) ->
  rmalloc_stmt_z -> rcalloc_stmt -> rfree_stmt ->
  (forall amsg msg, In (amsg, msg) ZERR_MSGS -> @fprintf_zerr_stmt_fl PState amsg msg) ->
  fwritex_stderr_stmt -> stdio_write_flush_stmt -> @fwrite_diag_stmt PState -> towrite_stmt ->
  fuzz_one_stmt FLM.
Proof.
  intros FLM FLIB WB LINKS MALLOCZ CALLOC FREE FPRINTF FWX SWF FWR TOW. unfold fuzz_one_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D payload AB lo errv
         HEAP BY FP WR RC D16 D0 DT PL HC SF AUX SPAB STK CEIL LO ERR MI FRM TP SP16 -> -> RAE SP47 PB.
  eapply (fuzz_one_call FLM FLIB MALLOCZ CALLOC FREE FPRINTF FWX SWF FWR TOW); try eassumption.
  intros NR fx. apply (LINKS fx payload NR FP).
Qed.
End CANSEC1.
