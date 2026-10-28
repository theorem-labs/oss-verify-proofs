(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit Printf_stdio_iface Lib_iface Driver_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation ctusegs := ImageCt.ctusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m' (wa a) <> None).

Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono ctusegs m m' -> agree_on (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. exact Ho.
Qed.

(* [comment removed for export] *)
Lemma agree_of_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> agree_on (rclient_addr LB SP) m m'.
Proof. intros LB SP m m' H. exact H. Qed.
Lemma agree_of_lx_pres : forall LB SP X m m', lx_pres LB SP X m m' -> agree_on (lx_client LB SP X) m m'.
Proof. intros LB SP X m m' H. exact H. Qed.
Lemma agree_of_drv_pres : forall LB SP m m', rdrv_pres LB SP m m' -> agree_on (lx_client LB SP DRVW) m m'.
Proof. intros LB SP m m' H. exact H. Qed.

Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at ctusegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at ctusegs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at ctusegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at ctusegs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells ctusegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells ctusegs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

Lemma stk_agree : forall P m m' lo hi,
  agree_on P m m' -> stk ctusegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk ctusegs m' lo hi.
Proof.
  intros P m m' lo hi HP ST HR. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Definition stdout_addr (a : Z) : Prop := (RSTDOUT <= a < RSTDOUT + 232) \/ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024).
Definition stderr_addr (a : Z) : Prop := RSTDERR <= a < RSTDERR + 232.
Definition ssp_addr (a : Z) : Prop := (got_ssp <= a < got_ssp + 8) \/ (ssp_guard <= a < ssp_guard + 8).
Definition lxs_addr (a : Z) : Prop :=
  (LX_GOT_STDERR <= a < LX_GOT_STDERR + 8) \/ (LX_STDERR_PTR <= a < LX_STDERR_PTR + 8).

Lemma stdout_file_agree : forall P m m' so,
  agree_on P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufb & FC & FL & BUF & BP & BL & INA).
  exists flags, mode, tail, bufb. split; [| split; [exact FL| split; [| auto]]].
  - eapply rw_cells_agree; [exact AG| exact FC|]. intros a Ha. apply HP. left. unfold file_cells in Ha. cbn in Ha. lia.
  - eapply rw_cells_agree; [exact AG| exact BUF|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_wfile_agree : forall P m m',
  agree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile m -> stderr_wfile m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & FC & FL). exists flags, mode, e, wend, tail. split; [| exact FL].
  eapply rw_cells_agree; [exact AG| exact FC|]. intros a Ha. apply HP. unfold stderr_addr. unfold file_cells in Ha. cbn in Ha. lia.
Qed.

Lemma ssp_cells_agree : forall P m m' c,
  agree_on P m m' -> (forall a, ssp_addr a -> P a) -> ssp_cells m c -> ssp_cells m' c.
Proof.
  intros P m m' c AG HP [H1 H2]. unfold ssp_cells, ssp_addr, got_ssp, ssp_guard in *. split.
  - eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. apply HP. cbn in Ha. lia.
  - eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. apply HP. cbn in Ha. lia.
Qed.

Lemma lx_statics_agree : forall P m m',
  agree_on P m m' -> (forall a, lxs_addr a -> P a) -> lx_statics m -> lx_statics m'.
Proof.
  intros P m m' AG HP (A1 & A2). unfold lx_statics.
  unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR in *.
  Ltac tr AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; cbn in Ha; lia].
  split; [tr AG HP A1| tr AG HP A2].
Qed.

Lemma rauxv_ok_agree : forall P m m' B,
  agree_on P m m' -> (forall a, B <= a -> P a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> P a) ->
  rauxv_ok m B -> rauxv_ok m' B.
Proof.
  intros P m m' B AG HP HC (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H).
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rw_cells_agree; [exact AG| exact C|]. intros a Ha. apply HC. cbn in Ha. lia.
  - eapply bytes_at_agree; [exact AG| exact A1|]. intros a Ha. apply HP. lia.
  - eapply bytes_at_agree; [exact AG| exact A2|]. intros a Ha. apply HP. cbn in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma stdout_addr_client : forall LB SP X a, stdout_addr a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof.
  intros LB SP X a Ha Hx. split; [exact Hx|]. right; right. unfold stdout_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
Qed.
Lemma stderr_addr_client : forall LB SP X a, stderr_addr a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof.
  intros LB SP X a Ha Hx. split; [exact Hx|]. right; right. unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
Qed.
Lemma lxs_addr_client : forall LB SP X a, lxs_addr a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof.
  intros LB SP X a Ha Hx. split; [exact Hx|]. right; right. unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP,
    LX_GOT_STDERR, LX_STDERR_PTR in *. lia.
Qed.
Lemma stack_client : forall LB SP X a, SP <= a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof. intros LB SP X a Ha Hx. split; [exact Hx| left; exact Ha]. Qed.
Lemma block_client : forall LB SP X b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof. intros LB SP X b a Hb Ha Hx. split; [exact Hx| right; left]. exists b. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma implM_get_bind : forall {A} (f : PState -> M PState A) s Q ms,
  implM ctusegs (f s) s Q ms -> implM ctusegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. unfold implM, mbind, mget in *. cbn. exact H. Qed.
Lemma implM_ret_bind : forall {A B} (a : A) (f : A -> M PState B) s Q ms,
  implM ctusegs (f a) s Q ms -> implM ctusegs (mbind (mret a) f) s Q ms.
Proof. intros A B a f s Q ms H. unfold implM, mbind, mret in *. cbn. exact H. Qed.
Lemma implM_upd_bind : forall {A} (g : PState -> PState) (k : unit -> M PState A) s Q ms,
  implM ctusegs (k tt) (g s) Q ms -> implM ctusegs (mbind (mupd g) k) s Q ms.
Proof. intros A g k s Q ms H. unfold implM, mbind, mupd in *. cbn. exact H. Qed.
Lemma implM_if : forall {A} (b : bool) (t e : M PState A) s Q ms,
  (b = true -> implM ctusegs t s Q ms) -> (b = false -> implM ctusegs e s Q ms) -> implM ctusegs (if b then t else e) s Q ms.
Proof. intros A b t e s Q ms Ht He. destruct b; auto. Qed.

(* [comment removed for export] *)
Lemma implM_frame_pure : forall {A} (c : M PState A) s Q (phi : Prop) ms,
  phi -> implM ctusegs c s Q ms -> implM ctusegs c s (fun a s' ms' => phi /\ Q a s' ms') ms.
Proof. intros A c s Q phi ms Hphi H. eapply implM_mono; [exact H|]. intros; split; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_at_read1 : forall m A bs (i : Z) b a,
  bytes_at ctusegs m A bs -> 0 <= i -> nth_error bs (Z.to_nat i) = Some b -> a = wa (A + i) ->
  ov_read_bytes ctusegs m a 1 = Some [b].
Proof.
  intros m A bs i b a HB Hi Hn ->.
  destruct (@nth_error_split _ bs (Z.to_nat i) b Hn) as (l1 & l2 & E & Hl1).
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia.
  rewrite (bytes_at_ov_read ctusegs m A bs (Z.to_nat i) 1 HB) by (rewrite E, length_app; cbn; lia).
  f_equal. rewrite E at 1. rewrite skipn_app, skipn_all2, Hl1, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma to_bytes_nth : forall (l : list Z) i c, nth_error l i = Some c -> nth_error (to_bytes l) i = Some (Z_to_bv 8 c).
Proof. intros l i c H. unfold to_bytes. rewrite nth_error_map, H. reflexivity. Qed.

Lemma znth_nth_error : forall (l : list Z) (i : Z), 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
  intros l i Hi. unfold znth, zlength in *. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (nth_error l (Z.to_nat i)) as [x|] eqn:E.
  - f_equal. symmetry. apply nth_error_nth. exact E.
  - apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis _ k => forall rsp, tall P (k rsp)
  end.

Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
  induction t as [[|r]|n k IH]; cbn; intros H HP.
  - exact I.
  - apply HP. exact H.
  - intros rsp. eapply IH; [apply H| exact HP].
Qed.

Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
  induction t as [[|a]|n k IH]; cbn; intros f H HF; [exact I| apply HF; exact H|].
  intros rsp. apply IH; [apply H| exact HF].
Qed.

Lemma impl_tall : forall {R} (t : itree node (exc R)) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
  impl ctusegs (at_node ctusegs) t (epost Q) ms -> tall P t ->
  impl ctusegs (at_node ctusegs) t (epost (fun r ms' => Q r ms' /\ P r)) ms.
Proof.
  intros R t. induction t as [[|r]|n k IH]; cbn; intros P Q ms H HP.
  - exact H.
  - eapply evt_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply Hk| apply HP].
Qed.

Section Keeps.
  Context {St B : Type} (f : St -> B).

  Definition keeps {A} (c : M St A) : Prop := forall s, tall (fun p => f (snd p) = f s) (c s).

  Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
  Proof. intros A a s. reflexivity. Qed.
  Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
  Proof. intros A s. exact I. Qed.
  Lemma keeps_get : keeps mget.
  Proof. intros s. reflexivity. Qed.
  Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
  Proof. intros g Hg s. cbn. apply Hg. Qed.
  Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
  Proof. intros A n dec s. cbn. intros rsp. destruct (dec rsp); cbn; [reflexivity| exact I]. Qed.
  Lemma keeps_bind : forall {A C} (m : M St A) (k : A -> M St C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
  Proof.
    intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
    eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
  Qed.
  Lemma keeps_getk : forall {C} (k : St -> M St C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
  Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
  Lemma keeps_loop : forall {X R} fuel (body : X -> M St (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
  Proof.
    induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
    apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
  Qed.
  Lemma keeps_if : forall {A} (b : bool) (m1 m2 : M St A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
  Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
End Keeps.
Arguments keeps {St B} f {A} c.

End WithCeiling0.
Ltac keeps_step :=
  first [ apply keeps_ret | apply keeps_unr | apply keeps_sys | apply keeps_get
        | apply keeps_getk | apply keeps_bind | apply keeps_if
        | apply keeps_upd; [intros; reflexivity] ].
Ltac keeps_tac :=
  repeat (intros; cbn beta;
          first [ solve [auto]
                | keeps_step
                | lazymatch goal with
                  | |- keeps _ (match ?x with _ => _ end) => destruct x
                  end ]).

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
Lemma implM_keepsf : forall {B A} (f : PState -> B) (c : M PState A) s Q ms,
  implM ctusegs c s Q ms -> keeps f c -> implM ctusegs c s (fun r s' ms' => Q r s' ms' /\ f s' = f s) ms.
Proof.
  intros B A0 f c s Q ms H K. unfold implM in *.
  eapply impl_epost_mono; [eapply impl_tall; [exact H| apply K]|]. cbn. intros [a s'] ms' [HQ E]. split; [exact HQ| exact E].
Qed.

(* [comment removed for export] *)
Definition but_so (s : PState) : PState := set_so_ps stdout_init s.

Lemma upd_so_keeps : forall g, keeps but_so (upd_so ps_so set_so_ps g).
Proof. intros g. unfold upd_so. apply keeps_upd. intros [? ? ? ?]; reflexivity. Qed.

Lemma stdio_writev_keeps : forall fd buf s0, keeps but_so (stdio_writev (St:=PState) fd buf s0).
Proof. intros fd buf s0. unfold stdio_writev. apply keeps_loop. intros x. unfold wv_body. keeps_tac. Qed.

Lemma stdout_writefn_keeps : forall l, keeps but_so (stdout_writefn ps_so set_so_ps l).
Proof.
  intros l. unfold stdout_writefn, stdout_stdio_write, rd_so. pose proof upd_so_keeps. pose proof stdio_writev_keeps. keeps_tac.
Qed.

Lemma stdout_vprintf_keeps : forall ps, keeps but_so (stdout_vprintf ps_so set_so_ps ps).
Proof.
  intros ps. unfold stdout_vprintf, stdout_towrite. apply keeps_bind; [apply upd_so_keeps|]. intros _.
  induction ps as [|pc ps IH]; cbn [out_pieces]; [apply keeps_ret|].
  apply keeps_bind; [| intros; exact IH].
  unfold stdout_fwritex, stdout_towrite, rd_so. pose proof upd_so_keeps. pose proof stdout_writefn_keeps. keeps_tac.
Qed.

Lemma but_so_eq : forall s s', but_so s' = but_so s -> ps_m s' = ps_m s /\ ps_brk s' = ps_brk s /\ ps_fa s' = ps_fa s.
Proof. intros [? ? ? ?] [? ? ? ?] E. unfold but_so, set_so_ps in E. cbn in E. injection E as -> -> ->. cbn. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RHEAP_frame_stmt : Prop := forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono ctusegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Definition RHEAP_block_range_stmt : Prop := forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Definition RHEAP_blocks_nodup_stmt : Prop := forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Definition RHEAP_blocks_disjoint_stmt : Prop := forall s LB m b1 b2,
  RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.

(* [comment removed for export] *)
Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m rr_guard.
Proof.
  intros s LB m (st & LB0 & _ & _ & MR & _). destruct MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & _) & _).
  unfold ssp_cells, got_ssp, ssp_guard. unfold RMallocRep.RGOT_SSP, RMallocRep.RSSP_GUARD in G4, G5. split; [exact G4| exact G5].
Qed.

Lemma bptr_eqb_eq : forall p q : bptr, bptr_eqb p q = true <-> p = q.
Proof.
  intros [[r o] z] [[r' o'] z']. unfold bptr_eqb, aptr_eqb. cbn [fst snd].
  rewrite !andb_true_iff, N.eqb_eq, !Z.eqb_eq. split; [intros [[-> ->] ->]; reflexivity| intros E; injection E as -> -> ->; auto].
Qed.

Lemma lb_remove_head : forall pb D n LB, List.NoDup (map blk_id ((pb, D, n) :: LB)) -> lb_remove pb ((pb, D, n) :: LB) = LB.
Proof.
  intros pb D n LB ND. cbn [map] in ND. inversion ND as [|x l NI ND']; subst. clear ND.
  unfold lb_remove. cbn. replace (bptr_eqb pb pb) with true by (symmetry; apply bptr_eqb_eq; reflexivity). cbn.
  induction LB as [|b LB IH]; [reflexivity|]. cbn.
  destruct (bptr_eqb (blk_id b) pb) eqn:E.
  - exfalso. apply NI. left. apply bptr_eqb_eq in E. exact E.
  - cbn. f_equal. apply IH; [intros Hin; apply NI; right; exact Hin| inversion ND'; assumption].
Qed.
End WithCeiling1.
