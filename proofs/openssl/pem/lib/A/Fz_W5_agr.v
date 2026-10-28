(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_M_malloc Fz_env Fz_M_free Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_W5_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma nth_error_upd_eq : forall {X} (l : list X) i x, (i < length l)%nat -> nth_error (upd l i x) i = Some x.
Proof. induction l as [|y l IH]; intros [|i] x H; cbn in *; [lia | lia | reflexivity | apply IH; lia]. Qed.
Lemma nth_error_upd_neq : forall {X} (l : list X) i j x, i <> j -> nth_error (upd l i x) j = nth_error l j.
Proof. induction l as [|y l IH]; intros [|i] [|j] x H; cbn in *; try reflexivity; [exfalso; exact (H eq_refl) | apply IH; congruence]. Qed.
Lemma skipn_upd_lt : forall {X} (l : list X) i j x, (i < j)%nat -> skipn j (upd l i x) = skipn j l.
Proof. induction l as [|y l IH]; intros [|i] [|j] x H; cbn in *; try reflexivity; try lia. apply IH; lia. Qed.
Lemma skipn_cons_nth : forall {X} (l : list X) i w, nth_error l i = Some w -> skipn i l = w :: skipn (S i) l.
Proof. induction l as [|y l IH]; intros [|i] w H; cbn in *; [discriminate | discriminate | injection H as ->; reflexivity | rewrite (IH i w H); reflexivity]. Qed.
Lemma all_zero_repeat : forall (l : list word) n, length l = n -> (forall j w, nth_error l j = Some w -> w = Z_to_bv 64 0) -> l = repeat (Z_to_bv 64 0) n.
Proof.
  induction l as [|y l IH]; intros [|n] L H; cbn in *; [reflexivity | discriminate | discriminate |].
  rewrite (H 0%nat y eq_refl). f_equal. apply IH; [lia|]. intros j w Hj. exact (H (S j) w Hj).
Qed.

(* [comment removed for export] *)
Lemma u8arr_agree_nw : forall (m m' : mem) A bs, u8arr asegs m A bs -> agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m' -> u8arr asegs m' A bs.
Proof. intros m m' A bs [B W] AG. split; [eapply bytes_at_agree; [exact B | exact AG] | eapply wr_at_agree_nw; [exact W | exact AG]]. Qed.
Lemma u32arr_agree_nw : forall (m m' : mem) A ws, u32arr asegs m A ws -> agree_on (fun x => A <= x < A + 4 * Z.of_nat (length ws)) m m' -> u32arr asegs m' A ws.
Proof.
  intros m m' A ws [B W] AG. split.
  - eapply bytes_at_agree; [exact B |]. intros x Hx. apply AG. cbv beta in *. rewrite u32s_length in Hx. lia.
  - eapply wr_at_agree_nw; [exact W |]. intros x Hx. apply AG. cbv beta in *. lia.
Qed.
Lemma es_rep_agree_nw : forall (m m' : mem) E top bot fl mk buf fs ls fn, es_rep m E top bot fl mk buf fs ls fn ->
  agree_on (fun x => E <= x < E + 904) m m' -> es_rep m' E top bot fl mk buf fs ls fn.
Proof.
  intros m m' E top bot fl mk buf fs ls fn R AG.
  destruct R as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  assert (AGs : forall (P : Z -> Prop), (forall x, P x -> E <= x < E + 904) -> agree_on P m m') by (intros P HP x Hx; apply AG; apply HP; exact Hx).
  unfold es_rep.
  split; [apply (u32arr_agree_nw m m' _ _ A1); apply AGs; intros x Hx; cbv beta in Hx; rewrite L1 in Hx; lia|]. split; [exact L1|].
  split; [apply (u32arr_agree_nw m m' _ _ A2); apply AGs; intros x Hx; cbv beta in Hx; rewrite L2 in Hx; lia|]. split; [exact L2|].
  split; [apply (u64arr_agree_nw asegs m m' _ _ A3); apply AGs; intros x Hx; cbv beta in Hx; rewrite L3 in Hx; lia|]. split; [exact L3|].
  split; [apply (u8arr_agree_nw m m' _ _ A4); apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia|].
  split; [apply (u8arr_agree_nw m m' _ _ A5); apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia|].
  split; [apply (u8arr_agree_nw m m' _ _ A6); apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia|].
  split; [apply (u64arr_agree_nw asegs m m' _ _ A7); apply AGs; intros x Hx; cbv beta in Hx; rewrite L7 in Hx; lia|]. split; [exact L7|].
  split; [apply (u32arr_agree_nw m m' _ _ A8); apply AGs; intros x Hx; cbv beta in Hx; rewrite L8 in Hx; lia|]. split; [exact L8|].
  split; [apply (u64arr_agree_nw asegs m m' _ _ A9); apply AGs; intros x Hx; cbv beta in Hx; rewrite L9 in Hx; lia|]. split; [exact L9|].
  split; [eapply rw_cells_agree_nw; [exact TB | apply AGs; intros x Hx; cbv beta in Hx; cbn [cells_size csize Nat.add] in Hx; lia]|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rmw (w : word) (live : list (Z * Z)) : list (Z * Z) := if bv_unsigned w =? 0 then live else live_remove (bv_unsigned w) live.
(* [comment removed for export] *)
Definition slot_free_ok (live : list (Z * Z)) (bad : list Z) (w : word) : Prop :=
  bv_unsigned w = 0 \/ ((exists n, In (bv_unsigned w, n) live) /\ ~ In (bv_unsigned w) bad).
(* [comment removed for export] *)
Fixpoint clr_rm (ws : list (word * word)) (live : list (Z * Z)) : list (Z * Z) :=
  match ws with [] => live | (wf, wn) :: ws' => clr_rm ws' (rmw wn (rmw wf live)) end.

Lemma rmw_sub : forall w live e, In e (rmw w live) -> In e live.
Proof. intros w live e. unfold rmw. destruct (bv_unsigned w =? 0); [tauto | apply live_remove_sub]. Qed.
Lemma rmw_keep : forall w live e, In e live -> fst e <> bv_unsigned w -> In e (rmw w live).
Proof. intros w live e H1 H2. unfold rmw. destruct (bv_unsigned w =? 0); [exact H1 | exact (live_remove_keep _ _ _ H1 H2)]. Qed.
Lemma clr_rm_sub : forall ws live e, In e (clr_rm ws live) -> In e live.
Proof. induction ws as [|[wf wn] ws IH]; intros live e H; cbn in H; [exact H | exact (rmw_sub _ _ _ (rmw_sub _ _ _ (IH _ _ H)))]. Qed.

(* [comment removed for export] *)
Lemma icstat_agree_nw : forall (m m' : mem) od, icstat m od -> (forall a k, 0xb9f200 <= a -> a + k <= 0xb9f2e8 -> agree_on (fun x => a <= x < a + k) m m') -> icstat m' od.
Proof.
  intros m m' od (A & B & C & D) AG. unfold icstat, G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in *.
  repeat split; (eapply rw_cells_agree_nw; [eassumption | apply AG; cbn [cells_size csize Nat.add]; lia]).
Qed.
Lemma errchain_agree_nw : forall (m m' : mem) k MK SA NODES E LV pad top ne, errchain m k MK SA NODES E LV pad top ne ->
  (forall a n, (0xb9f500 <= a /\ a + n <= 0xb9f528) \/ (TSD_MAIN_A + 8 <= a /\ a + n <= TSD_MAIN_A + 1024) \/ (MK <= a /\ a + n <= MK + 72) \/ (SA <= a /\ a + n <= SA + 32)
               \/ (NODES <= a /\ a + n <= NODES + 128) -> agree_on (fun x => a <= x < a + n) m m') -> errchain m' k MK SA NODES E LV pad top ne.
Proof.
  intros m m' k MK SA NODES E LV pad top ne (A & B & HK & C & D & G & HNE & HLV & H) AG. unfold errchain, G_TL_MASTER_ONCE, G_TL_MASTER_KEY, TSD_MAIN_A, sa_hdr in *.
  split; [eapply rw_cells_agree_nw; [exact A | apply AG; cbn [cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_agree_nw; [exact B | apply AG; cbn [cells_size csize Nat.add]; lia]|]. split; [exact HK|].
  split; [eapply rw_cells_agree_nw; [exact C | apply AG; cbn [cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_agree_nw; [exact D | apply AG; cbn [cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_agree_nw; [exact G | apply AG; cbn [cells_size csize Nat.add]; lia]|]. split; [exact HNE|]. split; [exact HLV|].
  eapply rw_cells_agree_nw; [exact H | apply AG; cbn [cells_size csize Nat.add]; lia].
Qed.
