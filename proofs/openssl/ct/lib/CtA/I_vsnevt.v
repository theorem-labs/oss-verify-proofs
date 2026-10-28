(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SFModel Arr SysStep FP ITree Nodes Decode. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import FX_lib F_memset F_memcpy F_fwritex F_snpf_pop_arg F_snpf_iface F_snpf_core.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import F_snpf_snsink F_snpf_sn_write F_towrite F_snpf_vfprintf F_snpf_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface R_small R_m2s R_thread I_consts I_qck F_achk X_atexit D_kit I_ikit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pck I_pcbits I_pchead I_pcfmt I_vprintfw I_vsntail I_vsnstmt I_pcxlist I_vsnfront I_vsnvf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_nonneg_ : forall {X} (l : list X), 0 <= zlength l.
Proof. intros X l. unfold zlength. lia. Qed.

Lemma length_zb_ : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

(* [comment removed for export] *)
Lemma zb8_zb : forall l, zb8 l = zb l.
Proof. intros l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zb_no_nul : forall body, Forall (fun c => 0 < c < 256) body -> ~ In z8 (zb body).
Proof.
  intros body FB IN. unfold zb in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
  pose proof (proj1 (Forall_forall _ _) FB c Hc) as R. cbn beta in R.
  apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
  change (2 ^ Z.of_N 8) with 256 in E. rewrite Z.mod_small in E by lia. change (bv_unsigned z8) with 0 in E. lia.
Qed.

Lemma forall_body_fmt : forall body, Forall (fun c => 0 < c < 256) body -> Forall (fun c => 0 <= c < 256) (body ++ [0]).
Proof.
  intros body FB. apply Forall_app. split; [| constructor; [lia| constructor]].
  eapply Forall_impl; [| exact FB]. intros c Hc. cbn beta in Hc. lia.
Qed.

(* [comment removed for export] *)
Lemma va_area_nth : forall m VA slots i w, va_area m VA slots -> nth_error slots i = Some w ->
  ro_cells ctasegs m (VA + 8 * Z.of_nat i) [C8 w].
Proof.
  intros m VA slots. revert VA. induction slots as [|w0 slots IH]; intros VA i w H Hn; [destruct i; discriminate|].
  unfold va_area in H. cbn [u64s] in H. apply bytes_at_app in H. destruct H as [H1 H2]. rewrite length_le8 in H2.
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. replace (VA + 8 * Z.of_nat 0) with VA by lia.
    split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H1.
  - cbn in Hn. replace (VA + 8 * Z.of_nat (S i)) with ((VA + Z.of_nat 8) + 8 * Z.of_nat i) by lia.
    apply (IH (VA + Z.of_nat 8) i w); [exact H2| exact Hn].
Qed.

(* [comment removed for export] *)
Lemma va_of_rw5 : forall m A w1 w2 w3 w4 w5, rw_cells ctasegs m A [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5] -> va_area m A [w1; w2; w3; w4; w5].
Proof. intros m A w1 w2 w3 w4 w5 [[_ H] _]. unfold va_area. cbn [u64s cells_bytes cbytes] in *. exact H. Qed.

(* [comment removed for export] *)
Lemma u64s_app5 : forall (w1 w2 w3 w4 w5 : word) stk, u64s ([w1; w2; w3; w4; w5] ++ stk) = u64s [w1; w2; w3; w4; w5] ++ u64s stk.
Proof. intros. cbn [u64s app]. rewrite <- !app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_cells_drop7 : forall m A c0 c1 c2 c3 c4 c5 c6 cs,
  rw_cells ctasegs m A (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: cs) ->
  rw_cells ctasegs m (A + Z.of_nat (cells_size [c0; c1; c2; c3; c4; c5; c6])) cs.
Proof.
  intros m A c0 c1 c2 c3 c4 c5 c6 cs H.
  change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: cs) with ([c0; c1; c2; c3; c4; c5; c6] ++ cs) in H.
  apply F_fwritex.rw_cells_app in H. exact (proj2 H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition evarg_ok (m : mem) (lo bnd D dn : Z) (slot : word) (a : parg) (cov : option Z) : Prop :=
  match a with
  | PA_s s =>
      (exists slack : list byte,
        bytes_at ctasegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
        /\ Forall (fun c => 0 < c < 256) s
        /\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
        /\ 0 < bv_unsigned slot /\ bv_unsigned slot + zlength s + 1 + zlength slack <= USTACK_TOP - 16
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ bnd <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= D \/ D + dn <= bv_unsigned slot)
        /\ chkr m (bv_unsigned slot) (zlength s + 1))
      \/ (exists p, cov = Some p /\ 0 < p <= zlength s       (* [comment removed for export] *)
        /\ bytes_at ctasegs m (bv_unsigned slot) (zb s)
        /\ Forall (fun c => 0 < c < 256) s
        /\ 0 < bv_unsigned slot /\ bv_unsigned slot + zlength s <= USTACK_TOP - 16
        /\ (bv_unsigned slot + zlength s <= lo \/ bnd <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s <= D \/ D + dn <= bv_unsigned slot)
        /\ chkr m (bv_unsigned slot) p)
  | PA_sn => bv_unsigned slot = 0
  | PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
  | PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
  | PA_z u => bv_unsigned slot = u
  | PA_g _ => False
  end.

Fixpoint evargs_ok (m : mem) (lo bnd D dn : Z) (slots : list word) (args : list parg) (covs : list (option Z)) : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => False
                  | w :: slots' => evarg_ok m lo bnd D dn w a (vhd_cov covs) /\ evargs_ok m lo bnd D dn slots' args' (tl covs)
                  end
  end.

Lemma evargs_mono : forall m lo bnd bnd' D dn slots args covs,
  evargs_ok m lo bnd D dn slots args covs -> bnd' <= bnd -> evargs_ok m lo bnd' D dn slots args covs.
Proof.
  intros m lo bnd bnd' D dn slots args. revert slots.
  induction args as [|a args IH]; intros slots covs H LE; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH _ _ H2 LE)].
  destruct a as [str| |i|u|u|d]; cbn [evarg_ok] in H1 |- *; try exact H1.
  destruct H1 as [(sl & BY & FB & PAD & P0 & HI & SEP & SEPD & CK) | (p & Ep & Hp & BY & FB & P0 & HI & SEP & SEPD & CK)].
  - left. exists sl. repeat (split; [first [assumption | lia]|]). exact CK.
  - right. exists p. repeat (split; [first [assumption | lia]|]). exact CK.
Qed.

(* [comment removed for export] *)
Lemma evargs_xfer : forall m m' lo bnd D dn slots args covs,
  evargs_ok m lo bnd D dn slots args covs -> munch [(lo, bnd); (D, D + dn)] m m' ->
  SHADOW_HI <= lo -> (D + dn <= SHADOW_LO \/ SHADOW_HI <= D) ->
  evargs_ok m' lo bnd D dn slots args covs.
Proof.
  intros m m' lo bnd D dn slots args. revert slots.
  induction args as [|a args IH]; intros slots covs H MU HSH DSH; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH _ _ H2 MU HSH DSH)].
  destruct a as [str| |i|u|u|d]; cbn [evarg_ok] in H1 |- *; try exact H1.
  destruct H1 as [(sl & BY & FB & PAD & P0 & HI & SEP & SEPD & CK) | (p & Ep & Hp & BY & FB & P0 & HI & SEP & SEPD & CK)].
  - left. exists sl.
    split. { apply (bytes_at_transport ctasegs _ m m' _ _ BY MU). cbn [disjoint_from]. rewrite length_app, length_zb_. cbn [length].
             unfold zlength in *. lia. }
    repeat (split; [first [assumption | lia]|]).
    apply (chkr_munch _ m m' _ _ CK MU). intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in *. lia.
  - right. exists p.
    split; [exact Ep|]. split; [exact Hp|].
    split. { apply (bytes_at_transport ctasegs _ m m' _ _ BY MU). cbn [disjoint_from]. rewrite length_zb_. unfold zlength in *. lia. }
    repeat (split; [first [assumption | lia]|]).
    apply (chkr_munch _ m m' _ _ CK MU). intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in *. lia.
Qed.

(* [comment removed for export] *)
Lemma evargs_ck : forall m lo bnd D dn slots args covs, evargs_ok m lo bnd D dn slots args covs -> ck_args m lo bnd slots args covs.
Proof.
  intros m lo bnd D dn slots args. revert slots.
  induction args as [|a args IH]; intros slots covs H; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH _ _ H2)].
  destruct a as [l| |i|u|u|d]; cbn [evarg_ok ck_arg] in H1 |- *; try exact H1; try exact I.
  destruct (vhd_cov covs) as [cv|] eqn:EC; [exact I|].
  destruct H1 as [(sl & BY & FB & PAD & P0 & HI & SEP & SEPD & CK) | (p & Ep & _)]; [| discriminate Ep].
  exists (zb l).
  assert (LZ : Z.of_nat (length (zb l)) = zlength l) by (rewrite length_zb_; reflexivity).
  split. { split; [| exact (zb_no_nul l FB)].
           replace (zb l ++ Z_to_bv 8 0 :: sl) with ((zb l ++ [z8]) ++ sl) in BY by (rewrite <- app_assoc; reflexivity).
           apply bytes_at_app in BY. exact (proj1 BY). }
  split; [exact P0|]. split; [rewrite LZ; lia|]. split; [rewrite LZ; unfold USTACK_TOP in HI; lia|].
  rewrite LZ. exact CK.
Qed.

(* [comment removed for export] *)
Definition cov_le (xs ys : list (option Z)) : Prop :=
  forall i p, nth_error xs i = Some (Some p) -> nth_error ys i = Some (Some p).
Lemma cov_le_hd : forall xs ys p, cov_le xs ys -> vhd_cov xs = Some p -> vhd_cov ys = Some p.
Proof.
  intros xs ys p H E. destruct xs as [|x xs]; [discriminate E|]. cbn in E. subst x.
  pose proof (H 0%nat p eq_refl) as H0. destruct ys as [|y ys]; [discriminate H0|]. cbn in H0 |- *. congruence.
Qed.
Lemma cov_le_tl : forall xs ys, cov_le xs ys -> cov_le (tl xs) (tl ys).
Proof.
  intros xs ys H i p E. destruct xs as [|x xs]; [destruct i; discriminate E|]. cbn in E.
  pose proof (H (S i) p E) as H1. destruct ys as [|y ys]; [discriminate H1|]. exact H1.
Qed.
Lemma cov_le_none_cons : forall xs ys, cov_le xs (tl ys) -> cov_le (None :: xs) ys.
Proof.
  intros xs ys H i p E. destruct i as [|i]; [discriminate E|]. cbn in E. pose proof (H i p E) as H1.
  destruct ys as [|y ys]; [destruct i; discriminate H1| exact H1].
Qed.
Lemma cov_le_hd_cons : forall xs ys, cov_le xs (tl ys) -> cov_le (vhd_cov ys :: xs) ys.
Proof.
  intros xs ys H i p E. destruct i as [|i].
  - cbn in E. destruct ys as [|y ys]; [discriminate E|]. cbn in E |- *. exact E.
  - cbn in E. pose proof (H i p E) as H1. destruct ys as [|y ys]; [destruct i; discriminate H1| exact H1].
Qed.
Lemma cov_le_nil : forall ys, cov_le [] ys.
Proof. intros ys i p E. destruct i; discriminate E. Qed.

(* [comment removed for export] *)
Lemma pcx_covs_le : forall fuel s args cin, cov_le (pcx_covs fuel s args cin) cin.
Proof.
  induction fuel as [|fuel IH]; intros s args cin; [apply cov_le_nil|].
  cbn [pcx_covs]. destruct s as [|c s']; [apply cov_le_nil|].
  destruct (c =? 0); [apply cov_le_nil|].
  destruct (c =? 37).
  - destruct (pcx_dir s') as [[[[ws pp] k] rest]|]; [| apply cov_le_nil].
    destruct ws.
    + destruct args as [|a0 args1]; [apply cov_le_nil|].
      destruct pp; [destruct args1 as [|a args3]; [apply cov_le_nil|] | destruct args1 as [|a args3]; [apply cov_le_nil|] | destruct args1 as [|a1 [|a args3]]; [apply cov_le_nil| apply cov_le_nil|]];
        cbn [app]; apply cov_le_none_cons.
      * destruct k; cbn [owncov]; first [apply cov_le_none_cons | apply cov_le_hd_cons]; apply IH.
      * destruct k; cbn [owncov]; first [apply cov_le_none_cons | apply cov_le_hd_cons]; apply IH.
      * apply cov_le_none_cons. destruct k; first [apply cov_le_hd_cons | apply cov_le_none_cons]; apply IH.
    + destruct pp; [destruct args as [|a args3]; [apply cov_le_nil|] | destruct args as [|a args3]; [apply cov_le_nil|] | destruct args as [|a1 [|a args3]]; [apply cov_le_nil| apply cov_le_nil|]];
        cbn [app].
      * destruct k; first [apply cov_le_hd_cons | apply cov_le_none_cons]; apply IH.
      * destruct k; first [apply cov_le_hd_cons | apply cov_le_none_cons]; apply IH.
      * apply cov_le_none_cons. destruct k; first [apply cov_le_hd_cons | apply cov_le_none_cons]; apply IH.
  - destruct ((0 <? c) && (c <? 256)); [apply IH| apply cov_le_nil].
Qed.

(* [comment removed for export] *)
Lemma evargs_args_okx : forall m lo bnd D dn slots args covs covsP,
  evargs_ok m lo bnd D dn slots args covs -> lo + 232 <= bnd -> cov_le covs covsP -> args_okx lo lo 0 m lo bnd lo slots args covsP.
Proof.
  intros m lo bnd D dn slots args. revert slots.
  induction args as [|a args IH]; intros slots covs covsP H LE CL; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH _ _ _ H2 LE (cov_le_tl _ _ CL))].
  destruct a as [str| |i|u|u|d]; cbn [evarg_ok arg_okx arg_ok] in H1 |- *; try exact H1; try contradiction.
  destruct H1 as [(sl & BY & FB & PAD & P0 & HI & SEP & SEPD & CK) | (p & Ep & Hp & BY & FB & P0 & HI & SEP & SEPD & CK)].
  - left. exists sl.
    split; [exact BY|]. split; [exact FB|]. split; [exact PAD|]. split; [exact P0|]. split; [exact SEP|].
    split; [destruct SEP; [left; lia| right; lia]|]. split; [destruct SEP; [left; lia| right; lia]|].
    split; [destruct SEP; [left; lia| right; lia]|]. exact CK.
  - right. change (hd_cov covsP) with (vhd_cov covsP). rewrite (cov_le_hd _ _ p CL Ep).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_zb_ in BB.
    split; [split; [exact Hp| exact CK]|]. split; [exact BY|]. split; [exact FB|]. split; [exact P0|]. split; [unfold zlength in *; unfold USTACK_TOP in HI; lia|].
    split; [exact SEP|]. split; [destruct SEP; [left; lia| right; lia]|]. split; [destruct SEP; [left; lia| right; lia]|].
    destruct SEP; [left; lia| right; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcg_ok_at : forall body args (cin : list (option Z)) slots (A VA lo bnd usp D dn : Z) m m',
  pcomx_ok (body ++ [0]) args = true -> Forall (fun c => 0 < c < 256) body -> (1 <= length body)%nat ->
  bytes_at ctasegs m A (zb (body ++ [0])) -> 0x10000 <= A -> A + zlength (body ++ [0]) <= STATIC_SPLIT ->
  chk_ok m A (zlength (body ++ [0])) ->
  va_area m VA slots -> usp <= VA -> VA + 8 * zlength slots <= USTACK_TOP - 16 -> (D + dn <= VA \/ VA + 8 * zlength slots <= D) ->
  evargs_ok m lo usp D dn slots args (pcx_covs (length (body ++ [0])) (body ++ [0]) args cin) ->
  pctx m -> pfcells m ->
  kHighShadowEnd + 8 <= lo -> lo <= bnd <= usp -> usp <= USTACK_TOP - 16 ->
  0 <= dn -> (D + dn <= 0x10000 \/ SEGTOP_A <= D) -> (D + dn <= SHADOW_LO \/ SHADOW_HI <= D) ->
  munch [(lo, usp); (D, D + dn)] m m' -> wmono ctasegs m m' ->
  pcg_ok body args slots A VA lo bnd m'.
Proof.
  intros body args cin slots A VA lo bnd usp D dn m m' OK FB L1 BY HA0 HA CHKA VAA QVA VAH DVA EV PCX PFC LOLO BND UHI DN0 DNS DSH MU WM.
  unfold STATIC_SPLIT, USTACK_TOP, SEGTOP_A, kHighShadowEnd, SHADOW_LO, SHADOW_HI in *.
  assert (LZF : zlength (body ++ [0]) = Z.of_nat (length body) + 1) by (unfold zlength; rewrite length_app; cbn [length]; lia).
  rewrite LZF in *.
  pose proof (u64s_length slots) as LU.
  assert (EV' : evargs_ok m' lo usp D dn slots args (pcx_covs (length (body ++ [0])) (body ++ [0]) args cin)).
  { apply (evargs_xfer m m' lo usp D dn slots args _ EV MU); unfold SHADOW_LO, SHADOW_HI; lia. }
  split; [exact OK|]. split; [exact FB|]. split; [exact L1|].
  split. { rewrite zb8_zb. apply (bytes_at_transport ctasegs _ m m' _ _ BY MU). cbn [disjoint_from].
           rewrite length_zb_, length_app. cbn [length]. lia. }
  split; [lia|]. split; [lia|].
  split. { eapply chk_ok_agree; [exact CHKA | lia | lia |]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. lia. }
  split. { intros i w Hn. apply (va_area_nth m' VA slots i w); [| exact Hn].
           unfold va_area. apply (bytes_at_transport ctasegs _ m m' _ _ VAA MU). cbn [disjoint_from]. rewrite LU.
           unfold zlength in *. lia. }
  split; [lia|]. split; [unfold zlength in *; lia|].
  split. { exists cin. apply (evargs_ck m' lo bnd D dn slots args). apply (evargs_mono m' lo usp bnd D dn slots args _ EV'). lia. }
  split.
  - apply (pctx_munch _ m m' PCX MU WM). intros x Hx. unfold in_PCR in Hx. cbn [outside]. lia.
  - apply (pfcells_munch _ m m' PFC MU WM). intros x Hx. unfold in_PFR in Hx. cbn [outside]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ivsn_post (usp D : Z) (o : list Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (zlength o)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
      /\ munch [(lo, usp); (D, D + (zlength o + 1))] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo usp
      /\ rw_cells ctasegs m' D [CB (Z.to_nat (zlength o + 1)) (zb o ++ [Z_to_bv 8 0])].

(* [comment removed for export] *)
Local Definition pbox (P : Prop) : Prop := P.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Local Ltac olia := unfold kHighShadowEnd, kHighMemEnd, USTACK_TOP, STATIC_SPLIT, SEGTOP_A in *;
  unfold zlength in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?Z2Nat.id by lia; first [lia | Z.div_mod_to_equations; lia].
Local Ltac shlia := intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia.

(* [comment removed for export] *)
Lemma ivsn_evt' : forall (usp D n A VA lo : Z) (body : list Z) (args : list parg) (slots : list word) (o : list Z) (junk : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem) (g : word),
  let fmt := body ++ [0] in
  stk ctasegs m lo usp -> lo <= usp - 8064 -> kHighShadowEnd + 8 <= lo -> usp <= USTACK_TOP - 16 -> usp mod 16 = 0 ->
  (* [comment removed for export] *)
  bytes_at ctasegs m A (zb fmt) -> Forall (fun c => 0 < c < 256) body -> (1 <= length body)%nat ->
  0x10000 <= A -> A + zlength fmt <= STATIC_SPLIT -> chkr m A (zlength fmt) ->
  pass1x_ok fmt = true -> printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (zlength o, o)) ->
  fp_callsx (length fmt) fmt args = [] -> pcomx_ok fmt args = true ->
  (* [comment removed for export] *)
  va_area m VA slots -> usp <= VA -> VA + 8 * zlength slots <= USTACK_TOP - 16 ->
  (D + (zlength o + 1) <= VA \/ VA + 8 * zlength slots <= D) ->
  evargs_ok m lo usp D (zlength o + 1) slots args (vcovs fmt args) ->
  (* [comment removed for export] *)
  1 <= n -> n < 2^31 -> zlength o <= n - 1 -> 0 < D -> D + n <= USTACK_TOP - 16 -> (D + n <= 0x10000 \/ SEGTOP_A <= D) ->
  rw_cells ctasegs m D [CB (Z.to_nat (zlength o + 1)) junk] -> chkr m D (zlength o + 1) ->
  (D + (zlength o + 1) <= lo \/ usp <= D) ->
  (* [comment removed for export] *)
  ictx m -> (forall p k, lo <= p -> p + k <= usp -> chkr m p k) -> rod_chk m -> pfcells m -> vsncells m -> ssp_cells m g ->
  mem_inv ctasegs m ->
  evt ctasegs (ivsn_post usp D o ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b24d4) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until g. cbv zeta.
  intros ST LO LOLO UHI U16 BY FB L1 HA0 HA FMTC P1 MODEL FPC OK VAA QVA VAH DVA EV Hn N31 OLE D0 DH DNS DST CHD DSEP
         IC STKC ROD PFC VSN SSP MI.
  pose proof (zlength_nonneg_ o) as O0.
  assert (LZF : zlength (body ++ [0]) = Z.of_nat (length body) + 1) by (unfold zlength; rewrite length_app; cbn [length]; lia).
  assert (PCX : pctx m) by (destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S); split; [exact M2S| split; assumption]).
  pose proof (chkr_bound _ _ _ CHD) as (DB0 & DB1).
  pose proof CHD as (_ & _ & (RIMD & _)). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIMD.
  assert (DSH : D + (zlength o + 1) <= SHADOW_LO \/ SHADOW_HI <= D) by (unfold SHADOW_LO, SHADOW_HI; lia).
  pose proof (u64s_length slots) as LU.
  unfold kHighShadowEnd, kHighMemEnd, USTACK_TOP, STATIC_SPLIT, SEGTOP_A in *.
  (* [comment removed for export] *)
  assert (PCG0 : pcg_ok body args slots A VA lo usp m).
  { eapply (pcg_ok_at body args (arg_covs (length (body ++ [0])) (body ++ [0]) args) slots A VA lo usp usp D (zlength o + 1) m m); try eassumption;
      unfold kHighShadowEnd, USTACK_TOP, STATIC_SPLIT, SEGTOP_A; try lia.
    - first [exact (chkr_chk_ok _ _ _ FMTC) | rewrite LZF; exact (chkr_chk_ok _ _ _ FMTC) | rewrite <- LZF; exact (chkr_chk_ok _ _ _ FMTC)].
    - apply munch_refl.
    - apply wmono_refl. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (ivsn_walkA' RIP usp D n A VA lo body args slots);
      first [exact ST | exact PCG0 | exact VSN | exact MI | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms1 P. unfold ivsnA_post in P.
  destruct P as (m1 & u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & j8 & junkf & -> & MU1 & WM1 & MI1 & ST1 & FRt & FRb).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (rw_cells_transport ctasegs _ _ _ _ _ DST MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as DST1.
  assert (VAA1 : va_area m1 VA slots).
  { unfold va_area in VAA |- *. apply (bytes_at_transport ctasegs _ m m1 _ _ VAA MU1). cbn [disjoint_from]. rewrite LU. unfold zlength in *. lia. }
  assert (BY1 : bytes_at ctasegs m1 A (zb (body ++ [0]))).
  { apply (bytes_at_transport ctasegs _ m m1 _ _ BY MU1). cbn [disjoint_from]. rewrite length_zb_. unfold zlength in *. lia. }
  destruct SSP as (SSP1 & SSP2). unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (ro_cells_transport ctasegs _ _ _ _ _ SSP1 MU1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as SSP1'.
  pose proof (ro_cells_transport ctasegs _ _ _ _ _ SSP2 MU1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as SSP2'.
  (* [comment removed for export] *)
  assert (MUX : forall m', munch (VSN_W lo (usp + -2160) D (Z.to_nat (zlength o + 1))) m1 m' -> munch [(lo, usp); (D, D + (zlength o + 1))] m m').
  { intros m' MU'. apply (munch_trans _ m m1 m').
    - eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros x Hx; cbn [outside] in *. lia.
    - eapply munch_weaken; [| exact MU']. unfold sub_fp, VSN_W; intros x Hx; cbn [outside] in *. rewrite ?Z2Nat.id in * by lia. lia. }
  assert (MUXW : forall m', munch (VSN_W lo (usp + -2160) D (Z.to_nat (zlength o + 1))) m1 m' -> wmono ctasegs m1 m' -> wmono ctasegs m m').
  { intros m' _ WM'. exact (wmono_trans _ _ _ _ WM1 WM'). }
  pose proof (vsnprintf_proof RIP PCG PCG_mono (ivfsn_gen RIP)) as VS. unfold vsnprintf_stmt in VS. cbv zeta in VS.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply VS with (F := F) (fc := fc) (m := m1) (D := D) (n := n) (A := A) (VA := VA) (dn := Z.to_nat (zlength o + 1)) (junkd := junk)
               (fmt := body ++ [0]) (slots := slots) (args := args) (lo := lo) (canary := g) (r := zlength o) (o := o)
               (F0 := lo) (B0 := lo) (BS0 := 0) (ap0 := lo);
      clear VS; rewrite ?EU2160; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd.
    all: first [ reflexivity | exact DST1 | exact BY1 | exact (forall_body_fmt body FB) | exact P1 | exact VAA1 | exact MODEL | exact FPC | exact ST1
               | (split; [exact SSP1' | exact SSP2']) | exact MI1 | exact I
               | ((* [comment removed for export] *)
                  lazymatch goal with |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac
                                    | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac | |- @eq Z _ _ => idtac
                                    | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac | |- @eq nat _ _ => idtac | |- _ \/ _ => idtac end;
                  olia)
               | idtac ].
    - (* [comment removed for export] *)
      intros m' MU'. pose proof (MUX m' MU') as MUm.
      apply (evargs_args_okx m' lo (usp + -2160) D (zlength o + 1) slots args (vcovs (body ++ [0]) args)); [| lia | unfold vcovs; apply pcx_covs_le].
      apply (evargs_mono m' lo usp (usp + -2160) D (zlength o + 1) slots args); [| lia].
      apply (evargs_xfer m m' lo usp D (zlength o + 1) slots args _ EV MUm); unfold SHADOW_LO, SHADOW_HI in *; lia.
    - apply (ictx_munch _ m m1 IC MU1 WM1). intros x Hx; cbn [in_rl ICR outside] in *. lia.
    - intros p n' H1 H2. apply (chkr_munch _ m m1 p n' (STKC p n' H1 ltac:(lia)) MU1).
      intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *. lia.
    - apply (chkr_munch _ m m1 _ _ FMTC MU1). intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *. lia.
    - destruct ROD as (R1 & R2 & R3). split; [| split]; [apply (chkr_munch _ m m1 _ _ R1 MU1) | apply (chkr_munch _ m m1 _ _ R2 MU1)
        | apply (chkr_munch _ m m1 _ _ R3 MU1)]; intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia.
    - apply (chkr_munch _ m m1 _ _ (chkr_sub _ _ _ D (zlength o) CHD ltac:(lia) ltac:(lia) ltac:(lia)) MU1).
      intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *. lia.
    - (* [comment removed for export] *)
      intros m' MU' WM'. exists body. split; [reflexivity|].
      eapply (pcg_ok_at body args (arg_covs (length (body ++ [0])) (body ++ [0]) args) slots A VA lo (usp + -2160) usp D (zlength o + 1) m m'); try eassumption;
        unfold kHighShadowEnd, USTACK_TOP, STATIC_SPLIT, SEGTOP_A, SHADOW_LO, SHADOW_HI; try lia.
      + first [exact (chkr_chk_ok _ _ _ FMTC) | rewrite LZF; exact (chkr_chk_ok _ _ _ FMTC) | rewrite <- LZF; exact (chkr_chk_ok _ _ _ FMTC)].
      + exact (MUX m' MU').
      + exact (MUXW m' MU' WM'). }
  cbv beta. intros ms2 P. unfold vsnprintf_post in P. rewrite ?EU2160 in P.
  destruct P as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & Ft & fc' & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FOK2
                 & ST2 & SSP' & DST2).
  unfold VSN_W in MU2.
  pose proof (rw_cells_transport ctasegs _ _ _ _ _ FRt MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRt2.
  pose proof (rw_cells_transport ctasegs _ _ _ _ _ FRb MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRb2.
  pose proof (MUX m2 MU2) as MU12. pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
  assert (CHK2' : chk_ok m2 D (zlength o + 1)).
  { apply chkr_chk_ok. apply (chkr_munch _ m m2 _ _ CHD MU12). intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *. lia. }
  assert (M2S2 : m2s_cells m2).
  { pose proof (ictx_munch _ m m2 IC MU12 WM12 ltac:(intros x Hx; cbn [in_rl ICR outside] in *; lia)) as (_ & _ & _ & X). exact X. }
  replace (ret_pc (Z_to_bv 64 0x1b2568)) with (Z_to_bv 64 0x1b2568) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* [comment removed for export] *)
  eapply evt_mono.
  { eapply (ivsn_walkC RIP usp D n (zlength o) lo j8 junkf);
      first [exact ST2 | exact FRt2 | exact FRb2 | exact CHK2' | exact M2S2 | exact MI2 | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms3 (m3 & w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & -> & MU3 & WM3 & MI3 & ST3).
  exists m3, w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, Ft, fc'. split; [reflexivity|].
  split. { apply (munch_trans _ m m2 m3); [exact MU12|].
           eapply munch_weaken; [| exact MU3]. unfold sub_fp; intros x Hx; cbn [outside] in *. lia. }
  split; [exact (wmono_trans _ _ _ _ WM12 WM3)|]. split; [exact MI3|]. split; [exact ST3|].
  pose proof (rw_CB_length _ _ _ _ DST) as LJ.
  assert (LJ' : (length junk <= S (length o))%nat) by (rewrite LJ; unfold zlength; lia).
  rewrite (skipn_all2 junk LJ') in DST2.
  apply (rw_cells_transport ctasegs _ _ _ _ _ DST2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma ivsn_evt : forall (usp D n A VA lo : Z) (body : list Z) (args : list parg) (slots : list word) (o : list Z) (junk : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem) (g : word),
  let fmt := body ++ [0] in
  stk ctasegs m lo usp -> lo <= usp - 8064 -> kHighShadowEnd + 8 <= lo -> usp <= USTACK_TOP - 16 -> usp mod 16 = 0 ->
  bytes_at ctasegs m A (zb fmt) -> Forall (fun c => 0 < c < 256) body -> (1 <= length body)%nat ->
  0x10000 <= A -> A + zlength fmt <= STATIC_SPLIT -> chkr m A (zlength fmt) ->
  pass1x_ok fmt = true -> printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (zlength o, o)) ->
  fp_callsx (length fmt) fmt args = [] -> pcomx_ok fmt args = true ->
  va_area m VA slots -> usp <= VA -> VA + 8 * zlength slots <= USTACK_TOP - 16 ->
  (D + (zlength o + 1) <= VA \/ VA + 8 * zlength slots <= D) ->
  evargs_ok m lo usp D (zlength o + 1) slots args (vcovs fmt args) ->
  1 <= n -> n < 2^31 -> zlength o <= n - 1 -> 0 < D -> D + n <= USTACK_TOP - 16 -> (D + n <= 0x10000 \/ SEGTOP_A <= D) ->
  rw_cells ctasegs m D [CB (Z.to_nat (zlength o + 1)) junk] -> chkr m D (zlength o + 1) ->
  (D + (zlength o + 1) <= lo \/ usp <= D) ->
  ictx m -> (forall p k, lo <= p -> p + k <= usp -> chkr m p k) -> rod_chk m -> pfcells m -> vsncells m -> ssp_cells m g ->
  mem_inv ctasegs m ->
  evt ctasegs (ivsn_post usp D o ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad66c) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until g. cbv zeta. intros.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  lstep.
  apply (ivsn_evt' usp D n A VA lo body args slots o junk) with (g := g); assumption.
Qed.

(* [comment removed for export] *)
Lemma isn_evt : forall (usp D n A lo : Z) (body : list Z) (stw : list word) (args : list parg) (o : list Z) (junk : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem) (g : word),
  let fmt := body ++ [0] in
  stk ctasegs m lo usp -> lo <= usp - 8160 -> kHighShadowEnd + 8 <= lo -> usp <= USTACK_TOP - 16 -> usp mod 16 = 0 ->
  bytes_at ctasegs m A (zb fmt) -> Forall (fun c => 0 < c < 256) body -> (1 <= length body)%nat ->
  0x10000 <= A -> A + zlength fmt <= STATIC_SPLIT -> chkr m A (zlength fmt) ->
  pass1x_ok fmt = true -> printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (zlength o, o)) ->
  fp_callsx (length fmt) fmt args = [] -> pcomx_ok fmt args = true ->
  (* [comment removed for export] *)
  va_area m usp stw -> usp + 8 * zlength stw <= USTACK_TOP - 16 -> (stw = [] \/ D + n <= usp \/ usp + 8 * zlength stw <= D) ->
  evargs_ok m lo usp D (zlength o + 1) ([a3; a4; a5; a6; a7] ++ stw) args (vcovs fmt args) ->
  1 <= n -> n < 2^31 -> zlength o <= n - 1 -> 0 < D -> D + n <= USTACK_TOP - 16 -> (D + n <= 0x10000 \/ SEGTOP_A <= D) ->
  rw_cells ctasegs m D [CB (Z.to_nat (zlength o + 1)) junk] -> chkr m D (zlength o + 1) ->
  (D + (zlength o + 1) <= lo \/ usp <= D) ->
  ictx m -> (forall p k, lo <= p -> p + k <= usp -> chkr m p k) -> rod_chk m -> pfcells m -> vsncells m -> ssp_cells m g ->
  mem_inv ctasegs m ->
  evt ctasegs (ivsn_post usp D o ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad674) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until g. cbv zeta.
  intros ST LO LOLO UHI U16 BY FB L1 HA0 HA FMTC P1 MODEL FPC OK VST STH STD EV Hn N31 OLE D0 DH DNS DST CHD DSEP
         IC STKC ROD PFC VSN SSP MI.
  pose proof (zlength_nonneg_ o) as O0. pose proof (u64s_length stw) as LU. pose proof (zlength_nonneg_ stw) as STK0.
  assert (STD' : 8 * zlength stw = 0 \/ D + n <= usp \/ usp + 8 * zlength stw <= D) by (destruct STD as [->|X]; [left; reflexivity| right; exact X]). clear STD.
  lazymatch type of VST with ?T => change T with (pbox T) in VST end.
  pose proof (chkr_bound _ _ _ CHD) as (DB0 & DB1).
  pose proof CHD as (_ & _ & (RIMD & _)). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIMD.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd, kHighMemEnd, USTACK_TOP, STATIC_SPLIT, SEGTOP_A in *.
  pose proof PFC as (AI & _).
  pose proof (munch_refl [(usp - 112, usp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  lazymatch type of BY with ?T => change T with (pbox T) in BY end.
  lstep.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB ctasegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xsteps_to 0x1cb8c8%Z.
  call try_init_spec; [exact AI | rewrite EU96; exact ST | rewrite EU96; lia | lia | assumption |].
  xsteps_to 0x1b24d4%Z.
  rename POST into ST.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  rename FR into FRs. unfold pbox in BY.
  pose proof (rw_cells_drop7 _ _ _ _ _ _ _ _ _ _ FRs) as VA5. cbn [cells_size csize Nat.add] in VA5.
  eapply evt_cut.
  { unfold pbox in VST.
    eapply (ivsn_evt' (usp + -96) D n A _ lo body args ([a3; a4; a5; a6; a7] ++ stw) o junk) with (g := g).
    all: lazymatch goal with
         | |- stk _ _ _ _ => first [rewrite <- EU96; exact ST | exact ST]
         | |- bytes_at _ _ _ _ => first [exact BY | apply (bytes_at_transport ctasegs _ m mA _ _ BY MU); cbn [disjoint_from]; rewrite length_zb_; unfold zlength in *; lia]
         | |- Forall _ _ => exact FB
         | |- chkr _ _ _ => first [apply (chkr_munch _ m mA _ _ FMTC MU); shlia | apply (chkr_munch _ m mA _ _ CHD MU); shlia]
         | |- pass1x_ok _ = _ => exact P1
         | |- printf_modelx _ _ _ _ _ = _ => exact MODEL
         | |- fp_callsx _ _ _ = _ => exact FPC
         | |- pcomx_ok _ _ = _ => exact OK
         | |- va_area _ ?va _ => unfold va_area; rewrite u64s_app5; apply bytes_at_app; split;
             [ apply va_of_rw5; replace va with (usp - 96 + 56) by lia; exact VA5
             | cbn [length u64s app]; rewrite ?length_app, ?length_le8; cbn [length Nat.add];
               replace (va + _) with usp by lia; unfold va_area in VST;
               apply (bytes_at_transport ctasegs _ m mA _ _ VST MU); cbn [disjoint_from]; rewrite LU; unfold zlength in *; lia ]
         | |- evargs_ok _ _ _ _ _ _ _ _ =>
             apply (evargs_mono mA lo usp (usp + -96) D (zlength o + 1)); [| lia];
             apply (evargs_xfer m mA lo usp D (zlength o + 1) _ _ _ EV); [| unfold SHADOW_LO, SHADOW_HI in *; lia | unfold SHADOW_LO, SHADOW_HI in *; lia];
             eapply munch_weaken; [| exact MU]; unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia
         | |- rw_cells _ _ _ _ => first [exact DST | apply (rw_cells_transport ctasegs _ _ _ _ _ DST MU WM); cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia]
         | |- ictx _ => apply (ictx_munch _ m mA IC MU WM); intros ?x ?Hx; cbn [in_rl ICR outside] in *; lia
         | |- forall p k, _ -> _ -> chkr _ p k => intros p k H1 H2; apply (chkr_munch _ m mA p k (STKC p k H1 ltac:(lia)) MU); shlia
         | |- rod_chk _ => destruct ROD as (R1 & R2 & R3); split; [| split];
                           [apply (chkr_munch _ m mA _ _ R1 MU) | apply (chkr_munch _ m mA _ _ R2 MU) | apply (chkr_munch _ m mA _ _ R3 MU)]; shlia
         | |- pfcells _ => apply (pfcells_munch _ m mA PFC MU WM); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; lia
         | |- vsncells _ => first [exact VSN | unfold vsncells in VSN |- *; apply (ro_cells_transport ctasegs _ _ _ _ _ VSN MU); cbn [disjoint_from cells_size csize Nat.add]; lia]
         | |- ssp_cells _ _ => destruct SSP as (SSP1 & SSP2); unfold got_ssp, ssp_guard in SSP1, SSP2; split;
                               [ first [exact SSP1 | apply (ro_cells_transport ctasegs _ _ _ _ _ SSP1 MU)]
                               | first [exact SSP2 | apply (ro_cells_transport ctasegs _ _ _ _ _ SSP2 MU)] ];
                               cbn [disjoint_from cells_size csize Nat.add]; lia
         | |- mem_inv _ _ => assumption
         | |- _ => idtac
         end.
    all: olia. }
  cbv beta. intros ms2 P. unfold ivsn_post in P.
  destruct P as (m2 & w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & Ft & fc' & -> & MU2 & WM2 & MI2 & ST2 & DST2).
  replace (ret_pc (Z_to_bv 64 0x1b291c)) with (Z_to_bv 64 0x1b291c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (rw_cells_transport ctasegs _ _ _ _ _ FRs MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRs2.
  assert (MU12 : munch [(lo, usp); (D, D + (zlength o + 1))] m m2).
  { apply (munch_trans _ m mA m2).
    - eapply munch_weaken; [| exact MU]. unfold sub_fp; intros xq Hxq; cbn [outside] in *. lia.
    - eapply munch_weaken; [| exact MU2]. unfold sub_fp; intros xq Hxq; cbn [outside] in *. lia. }
  pose proof (wmono_trans _ _ _ _ WM WM2) as WM12.
  clear MU WM. try clear ST. rename ST2 into ST.
  pose proof (munch_refl [(usp - 96, usp)] m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
  (* [comment removed for export] *)
  do 4 lstep.
  release_frame FRs2 ST usp.
  lstep. lstep.
  apply evt_done. unfold ivsn_post.
  exists m2. do 16 eexists. split; [reflexivity|].
  split; [exact MU12|]. split; [exact WM12|]. split; [assumption|]. split; [exact ST| exact DST2].
Qed.
End WithRIP.
