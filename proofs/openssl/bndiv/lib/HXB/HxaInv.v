(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SHBW_Z : wZ SHBW = SHB. Proof. reflexivity. Qed.
Lemma STK_Z : to_Z STK = 262144. Proof. reflexivity. Qed.
Lemma T_STK_Z : to_Z T_STK = 2. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition SH_LO : Z := 0x7fff7000.
Definition SH_HI : Z := 0x10007fff8000.

Lemma shad_range (a : Z) : 0 <= a < 2 ^ 47 -> SH_LO < shad a < SH_HI.
Proof.
  intros Ha. unfold shad, SHB, SH_LO, SH_HI. assert (0 <= a / 8) by (apply Z.div_pos; lia).
  assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma shad_add8 (a k : Z) : shad (a + 8 * k) = shad a + k.
Proof. unfold shad. rewrite (Z.mul_comm 8 k), Z.div_add by lia. ring. Qed.

Lemma shad_mono (a b : Z) : a <= b -> shad a <= shad b.
Proof. intros H. unfold shad. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition static_ok (a b : Z) (wr : bool) : Prop := In (a, b, wr) STATICS.

Definition IMGSH_LO : Z := 0x7fffa000.
Definition IMGSH_HI : Z := 0x80177a00.

Ltac cs_yes lo hi := split; [exists lo, hi; split; [cbn [In CLIENT_STATIC]; tauto | lia]
                            | intros (l0 & h0 & Hin0 & Hr0); cbn [In RT_STATIC] in Hin0;
                              repeat (destruct Hin0 as [Hin0|Hin0]; [injection Hin0 as <- <-; lia|]); contradiction].

(* [comment removed for export] *)
Lemma static_facts : forall a b wr, static_ok a b wr ->
  0x10000 <= a /\ a < b /\ b < 2 ^ 47
  /\ (b <= SEGTOP_A \/ (a = IMGSH_LO /\ b = IMGSH_HI))
  /\ (wr = true -> (forall x, a <= x < b -> client_static x) /\ In (a, b) LIBW_HXA)
  /\ ((0x10000 <= a /\ b <= 0x194000 /\ wr = false)
      \/ (RELRO_LO <= a /\ b <= RELRO_HI /\ wr = false)
      \/ (forall x, a <= x < b -> client_static x)
      \/ (a = g_shadow_memory_dynamic_address /\ b = a + 12 /\ wr = false)
      \/ (a = 0xbdadf8 /\ b = a + 8 /\ wr = false)
      \/ (a = IMGSH_LO /\ b = IMGSH_HI /\ wr = false)).
Proof.
  intros a b wr H. unfold static_ok, STATICS in H. cbn [In] in H.
  unfold SEGTOP_A, IMGSH_LO, IMGSH_HI, RELRO_LO, RELRO_HI, g_shadow_memory_dynamic_address.
  repeat (destruct H as [H|H]; [injection H as <- <- <-|]); try contradiction;
    (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [first [left; lia | right; split; reflexivity]|]);
    (split; [first [ discriminate | intros _; split; [intros x Hx; first [cs_yes 0x5e6630 0x6a0398 | cs_yes 0xbd6050 0xbfc730] | cbn [In LIBW_HXA]; tauto] ]|]);
    first [ left; repeat split; first [lia | reflexivity]
          | right; left; repeat split; first [lia | reflexivity]
          | right; right; left; intros x Hx; first [cs_yes 0x5e6630 0x6a0398 | cs_yes 0xbd6050 0xbfc730]
          | right; right; right; left; repeat split; first [lia | reflexivity]
          | right; right; right; right; left; repeat split; first [lia | reflexivity]
          | right; right; right; right; right; repeat split; first [lia | reflexivity] ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stk_okx (s : Z) : Prop := s mod 32 = 0 /\ 0 < s <= 262144.

Record xpar : Type := XP { xp_cbt : list (int * Z * bool); xp_cbw : list (Z * Z); xp_lw : list (Z * Z); xp_nbmax : Z; xp_rgsh : region; xp_stk : Z }.

Section Inv.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis PMc_mat : mat_stable PMc.
(* [comment removed for export] *)
Variable T : TSet.
(* [comment removed for export] *)
Variables (CL : list (Z * Z)) (lo sp0 r : Z) (m0 : word -> option byte) (cr0 anc : Z) (xp : xpar).
Hypothesis H_r : r = 0 \/ r = 16.
Hypothesis XP_ro : rg_wr (xp_rgsh xp) = false.
(* [comment removed for export] *)
Hypothesis XP_stk : stk_okx (xp_stk xp).

(* [comment removed for export] *)
Definition B0 : Z := sp0 - r - xp_stk xp.

Record ghost : Type := GH { g_S : rts RT }.

Definition J (g : ghost) (ms : machine_state) : Prop := forall c, ASTA RT (g_S g) PMc (eq ms) c -> realizes bsegs c T.

Lemma J_evt : forall g ms, evt bsegs (J g) ms -> J g ms.
Proof.
  intros g ms H c Hc.
  assert (Hcps : cps bsegs (ASTA RT (g_S g) PMc (eq ms)) (ASTA RT (g_S g) PMc (J g))).
  { unfold ASTA. apply (ast_evt bsegs SEGTOP_A asegs_wx asegs_below).
    - apply mat_stable_and; [exact (af_mat_stable RT AF (g_S g)) | exact PMc_mat].
    - intros ms' <-. exact H. }
  apply (Hcps T c Hc). intros c' Hc'. destruct (ASTA_unpack RT (g_S g) PMc (J g) c' Hc') as (ms' & HJ & Hc''). exact (HJ c' Hc'').
Qed.

(* [comment removed for export] *)
Definition rsize (M : HxMem.mem) (t : int) : Z := match mget M t with Some rg => to_Z (rg_size rg) | None => 0 end.

Definition blk_list (rho : valuation) (M : HxMem.mem) (tl : list int) : list (Z * Z) := map (fun t => (rho t, rsize M t)) tl.
Definition frm_list (rho : valuation) (tl : list int) : list (Z * nat) := map (fun t => (rho t, 0%nat)) tl.

Definition region_class (M : HxMem.mem) (bl fl : list int) : Prop :=
  forall t rg, mget M t = Some rg ->
    match rg_abs rg with
    | Some a => (to_Z a = 0 /\ to_Z (rg_size rg) = 0 /\ rg_wr rg = false)
                \/ ((exists w, static_ok (to_Z a) (to_Z a + to_Z (rg_size rg)) w /\ (rg_wr rg = true -> w = true))
                    /\ (to_Z a = IMGSH_LO -> rg = xp_rgsh xp)
                    /\ (rg_wr rg = true -> In (to_Z a, to_Z a + to_Z (rg_size rg)) (xp_lw xp)))
    | None => (t = T_STK /\ to_Z (rg_size rg) = xp_stk xp + r /\ rg_wr rg = true)
              \/ (t = sh_tag T_STK /\ to_Z (rg_size rg) = (xp_stk xp + r) / 8 /\ rg_wr rg = false)
              \/ (In t bl /\ rg_wr rg = true)
              \/ (exists b, In b bl /\ t = sh_tag b /\ to_Z (rg_size rg) = rsize M b / 8 /\ rg_wr rg = false)
              \/ (In t fl /\ to_Z (rg_size rg) = 56 /\ rg_wr rg = true)
              \/ (exists f, In f fl /\ t = sh_tag f /\ to_Z (rg_size rg) = 8 /\ rg_wr rg = true)
              (* [comment removed for export] *)
              \/ (exists n w, In (t, n, w) (xp_cbt xp) /\ to_Z (rg_size rg) = n /\ (rg_wr rg = true -> w = true))
              \/ (exists b n w, In (b, n, w) (xp_cbt xp) /\ t = sh_tag b /\ to_Z (rg_size rg) = n / 8 /\ rg_wr rg = false)
    end.

(* [comment removed for export] *)
Definition live_link (M : HxMem.mem) (bl fl : list int) : Prop :=
  (forall t, In t bl -> exists rg, mget M t = Some rg /\ rg_abs rg = None /\ rg_wr rg = true /\ 0 < to_Z (rg_size rg) /\ to_Z (rg_size rg) mod 8 = 0)
  /\ (forall t, In t fl -> exists rg, mget M t = Some rg /\ rg_abs rg = None /\ rg_wr rg = true /\ to_Z (rg_size rg) = 56).

(* [comment removed for export] *)
Definition caller_mem (a : Z) : Prop := aclient CL [] sp0 a /\ outside (xp_lw xp) a /\ outside (xp_cbw xp) a.

(* [comment removed for export] *)
Definition cb_inv (rho : valuation) (nx : int) : Prop :=
  forall t n w, In (t, n, w) (xp_cbt xp) ->
    In (rho t, n) CL /\ 0 < n /\ n mod 8 = 0 /\ tag_even t = true /\ (to_Z NEXT0 <= to_Z t /\ to_Z t + 1 < to_Z nx) /\ rho (sh_tag t) = shad (rho t)
    /\ (w = true -> In (rho t, rho t + n) (xp_cbw xp)).

Definition FMem (g : ghost) (rho : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte) : Prop :=
  let bl := x_blocks cd in let fl := x_frames cd in
  rt_live RT (g_S g) = blk_list rho M bl ++ CL
  /\ rt_frames RT (g_S g) = frm_list rho fl
  /\ List.NoDup (bl ++ fl)
  /\ (forall t, In t (bl ++ fl) -> tag_even t = true /\ to_Z NEXT0 <= to_Z t /\ to_Z t + 1 < to_Z nx)
  /\ (forall t rg, mget M t = Some rg -> to_Z t < to_Z nx)
  /\ to_Z NEXT0 <= to_Z nx /\ to_Z nx < 1000000
  /\ region_class M bl fl /\ live_link M bl fl
  /\ (rho T_STK = B0 /\ rho (sh_tag T_STK) = shad B0 /\ (forall t, In t (bl ++ fl) -> rho (sh_tag t) = shad (rho t))
      (* [comment removed for export] *)
      /\ 0 <= rho T_S0 < 2 ^ 64 /\ (rho T_S0 <= lo \/ rho T_S0 mod 8 <> 0 \/ 2 ^ 63 <= rho T_S0))
  /\ ART RT (g_S g) m /\ mem_inv bsegs m /\ stk bsegs m lo sp0
  /\ (rt_sp0 RT (g_S g) - STACK_WIN <= lo /\ lo <= B0 /\ sp0 + 16 <= USTACK_TOP /\ sp0 mod 32 = r)
  /\ (Z.of_nat (length CL) + xp_nbmax xp <= LIVE_MAX /\ Z.of_nat (length bl) = x_nb cd /\ 0 <= x_calls cd /\ cr0 - x_calls cd <= rt_credit RT (g_S g))
  /\ (forall a : word, caller_mem (bv_unsigned a) -> m a = m0 a)
  /\ rt_sp0 RT (g_S g) = anc
  /\ cb_inv rho nx.

Definition FInv (g : ghost) (rho : valuation) (cd : xcd) (S : sstate) (ms : machine_state) : Prop :=
  FMem g rho cd (s_mem S) (s_next S) (ms_mem ms) /\ ms_rom ms = seg_rom bsegs /\ regs_nf (ms_regs ms).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_not_outside : forall (W : list ivl) (a b x : Z), In (a, b) W -> a <= x < b -> ~ outside W x.
Proof.
  induction W as [|[lo' hi'] W IH]; intros a b x Hin Hx; [destruct Hin|]. cbn [outside]. intros [H1 H2].
  destruct Hin as [E|Hin]; [injection E as -> ->; lia | exact (IH a b x Hin Hx H2)].
Qed.

Lemma rsize_get (M : HxMem.mem) (t : int) (rg : region) : mget M t = Some rg -> rsize M t = to_Z (rg_size rg).
Proof. intros E. unfold rsize. rewrite E. reflexivity. Qed.

Lemma rsize_same_dirs (M M' : HxMem.mem) (t : int) : same_dirs M M' -> rsize M' t = rsize M t.
Proof.
  intros Hd. specialize (Hd t). unfold rsize. destruct (mget M t) as [rg|], (mget M' t) as [rg'|]; try contradiction; [|reflexivity].
  destruct Hd as (_ & Es & _). rewrite Es. reflexivity.
Qed.

Lemma blk_list_same_dirs (rho : valuation) (M M' : HxMem.mem) (tl : list int) : same_dirs M M' -> blk_list rho M' tl = blk_list rho M tl.
Proof. intros Hd. unfold blk_list. apply map_ext. intros t. rewrite (rsize_same_dirs M M' t Hd). reflexivity. Qed.

Lemma client_static_range (x : Z) : client_static x -> 0x5e6630 <= x < 0xbfc730.
Proof.
  intros [(l0 & h0 & Hin & Hr) _]. cbn [In CLIENT_STATIC] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). contradiction.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr_facts (g : ghost) (rho : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte)
    (t : int) (rg : region) (x : Z) :
  FMem g rho cd M nx m -> mget M t = Some rg -> rg_wr rg = true ->
  rbase rho t rg <= x < rbase rho t rg + to_Z (rg_size rg) ->
  aclient (rt_live RT (g_S g)) (rt_frames RT (g_S g)) B0 x /\ ~ caller_mem x /\ 0 <= x < 2 ^ 47.
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & Hcnt & Hagr & Hsp0a & Hcb)
         Eg Hw Hx.
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (af_sp0_win RT AF _ _ HART) as Hsp0w.
  pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1).
  assert (HCL : forall p n, In (p, n) CL -> 0 < p /\ p + n <= rt_sp0 RT (g_S g) - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p)).
  { intros p n Hin. apply (af_live_range RT AF _ _ p n HART). rewrite Hlive. apply in_or_app. right. exact Hin. }
  pose proof (Hcls t rg Eg) as C. destruct (rg_abs rg) as [a|] eqn:Ea; unfold rbase in Hx; rewrite Ea in Hx.
  - (* [comment removed for export] *)
    destruct C as [(_ & _ & C)|[(w & C & Cw) [_ Clw]]]; [congruence|]. rewrite (Cw Hw) in C.
    destruct (static_facts _ _ _ C) as (S1 & S2 & S3 & S4 & S5 & _). destruct (S5 eq_refl) as [Scs _].
    split; [right; left; apply Scs; lia|]. split; [|lia].
    intros (_ & Hout & _). exact (In_not_outside _ _ _ x (Clw Hw) ltac:(lia) Hout).
  - destruct C as [(-> & Es & _)|[(-> & _ & C)|[(Hin & _)|[(b & _ & _ & _ & C)|[(Hin & Es & _)|[(f & Hin & -> & Es & _)|[(n & w & Hin & Es & Cw)|(b & n & w & _ & _ & _ & C)]]]]]]]; try congruence.
    + (* [comment removed for export] *)
      rewrite Hrs, Es in Hx. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, B0 in *.
      split; [left; unfold USTACK_TOP; lia|]. split; [|lia].
      intros [[Hc|[Hc|[(p & n & Hin & Hr)|[(f & k & [] & _)|(f & k & [] & _)]]]] _]; [lia | apply client_static_range in Hc; lia |].
      destruct (HCL p n Hin) as (_ & Hp & _). lia.
    + (* [comment removed for export] *)
      assert (Hin' : In (rho t, rsize M t) (rt_live RT (g_S g))).
      { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists t. split; [reflexivity | exact Hin]. }
      rewrite (rsize_get M t rg Eg) in Hin'.
      destruct (af_live_range RT AF _ _ _ _ HART Hin') as (P1 & P2 & P3).
      split; [right; right; left; exists (rho t), (to_Z (rg_size rg)); split; [exact Hin' | exact Hx]|].
      assert (Hdisj : forall p n, In (p, n) CL -> rho t + to_Z (rg_size rg) <= p \/ p + n <= rho t).
      { intros p n Hin2. destruct (in_split t (x_blocks cd) Hin) as (l1 & l2 & El).
        assert (Esp : rt_live RT (g_S g) = map (fun t0 => (rho t0, rsize M t0)) l1 ++ (rho t, to_Z (rg_size rg)) :: (map (fun t0 => (rho t0, rsize M t0)) l2 ++ CL)).
        { rewrite Hlive. unfold blk_list. rewrite El, map_app. cbn [map]. rewrite (rsize_get M t rg Eg), <- app_assoc. reflexivity. }
        exact (af_live_disj RT AF _ _ _ _ p n _ _ HART Esp ltac:(apply in_or_app; right; apply in_or_app; right; exact Hin2)). }
      unfold SEGTOP_A, STACK_WIN, USTACK_TOP, B0 in *. split; [|lia].
      intros [[Hc|[Hc|[(p & n & Hin2 & Hr)|[(f & k & [] & _)|(f & k & [] & _)]]]] _]; [lia | apply client_static_range in Hc; lia |].
      destruct (Hdisj p n Hin2) as [D|D]; lia.
    + (* [comment removed for export] *)
      assert (Hin' : In (rho t, 0%nat) (rt_frames RT (g_S g))).
      { rewrite Hfr. unfold frm_list. apply in_map_iff. exists t. split; [reflexivity | exact Hin]. }
      destruct (af_frames_range RT AF _ _ _ _ HART Hin') as (P1 & P2 & P3 & P4).
      assert (P4' : forall p n, In (p, n) CL -> rho t + 64 <= p \/ p + n <= rho t).
      { intros p n Hin2. apply (P4 p n). rewrite Hlive. apply in_or_app. right. exact Hin2. }
      change (fs_size 0) with 64 in *. rewrite Es in Hx.
      split; [right; right; right; left; exists (rho t), 0%nat; split; [exact Hin' | change (fs_size 0) with 64; lia]|].
      unfold SEGTOP_A, STACK_WIN, USTACK_TOP, B0 in *. split; [|lia].
      intros [[Hc|[Hc|[(p & n & Hin2 & Hr)|[(f & k & [] & _)|(f & k & [] & _)]]]] _]; [lia | apply client_static_range in Hc; lia |].
      destruct (P4' p n Hin2) as [D|D]; lia.
    + (* [comment removed for export] *)
      assert (Hin' : In (rho f, 0%nat) (rt_frames RT (g_S g))).
      { rewrite Hfr. unfold frm_list. apply in_map_iff. exists f. split; [reflexivity | exact Hin]. }
      destruct (af_frames_range RT AF _ _ _ _ HART Hin') as (P1 & P2 & P3 & P4).
      destruct (af_fshadow_apart RT AF _ _ _ _ HART Hin') as [Q1 _].
      assert (Q1' : forall p n, In (p, n) CL -> p + n <= shad (rho f) \/ shad (rho f + 64) <= p).
      { intros p n Hin2. apply (Q1 p n). rewrite Hlive. apply in_or_app. right. exact Hin2. }
      change (fs_size 0) with 64 in *.
      rewrite (Hrsh f ltac:(apply in_or_app; right; exact Hin)), Es in Hx.
      assert (E8 : shad (rho f + 64) = shad (rho f) + 8) by (replace 64 with (8 * 8) by reflexivity; apply shad_add8).
      unfold SEGTOP_A, STACK_WIN, USTACK_TOP, B0 in *.
      pose proof (shad_range (rho f) ltac:(lia)) as Hsr. unfold SH_LO, SH_HI in Hsr.
      split; [right; right; right; right; exists (rho f), 0%nat; split; [exact Hin' | change (fs_size 0) with 64; lia]|]. split; [|lia].
      intros [[Hc|[Hc|[(p & n & Hin2 & Hr)|[(f' & k & [] & _)|(f' & k & [] & _)]]]] _]; [lia | apply client_static_range in Hc; lia |].
      destruct (Q1' p n Hin2) as [D|D]; lia.
    + (* [comment removed for export] *)
      destruct (Hcb t n w Hin) as (HinCL & Hn0 & Hn8 & Tev & Tr & Hsh & Hwcb).
      assert (Hin' : In (rho t, n) (rt_live RT (g_S g))) by (rewrite Hlive; apply in_or_app; right; exact HinCL).
      destruct (af_live_range RT AF _ _ _ _ HART Hin') as (P1 & P2 & P3). rewrite Es in Hx.
      split; [right; right; left; exists (rho t), n; split; [exact Hin' | exact Hx]|].
      unfold SEGTOP_A, STACK_WIN, USTACK_TOP, B0 in *. split; [|lia].
      intros (_ & _ & Hout). exact (In_not_outside _ _ _ x (Hwcb (Cw Hw)) Hx Hout).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma same_dirs_tags (M M' : HxMem.mem) (nx : int) :
  same_dirs M M' -> (forall t rg, mget M t = Some rg -> to_Z t < to_Z nx) -> (forall t rg, mget M' t = Some rg -> to_Z t < to_Z nx).
Proof.
  intros Hd H t rg' G'. specialize (Hd t). rewrite G' in Hd. destruct (mget M t) as [rg|] eqn:G; [|contradiction]. exact (H t rg G).
Qed.


Lemma same_dirs_class (M M' : HxMem.mem) (bl fl : list int) : same_dirs M M' -> ro_same M M' -> region_class M bl fl -> region_class M' bl fl.
Proof.
  intros Hd Hro H t rg' G'. pose proof (Hd t) as Hdt. rewrite G' in Hdt. destruct (mget M t) as [rg|] eqn:G; [|contradiction].
  destruct Hdt as (Ea & Es & _ & Ew & _). specialize (H t rg G). rewrite Ea, Es, Ew.
  destruct (rg_abs rg) as [a|].
  - destruct H as [H|(H1 & H2 & H3)]; [left; exact H|]. right. split; [exact H1|]. split; [|exact H3]. intros E. specialize (H2 E). subst rg.
    pose proof (Hro t (xp_rgsh xp) G XP_ro) as G2. congruence.
  - destruct H as [H|[H|[H|[(b & H1 & H2 & H3 & H4)|[H|[H|[H|H]]]]]]]; auto 8.
    right; right; right; left. exists b. rewrite (rsize_same_dirs M M' b Hd). auto.
Qed.

Lemma same_dirs_link (M M' : HxMem.mem) (bl fl : list int) : same_dirs M M' -> live_link M bl fl -> live_link M' bl fl.
Proof.
  intros Hd [H1 H2]. split; intros t Ht.
  - destruct (H1 t Ht) as (rg & G & Ea & Ew & Es). specialize (Hd t). rewrite G in Hd.
    destruct (mget M' t) as [rg'|]; [|contradiction]. destruct Hd as (Ea' & Es' & _ & Ew' & _). exists rg'. rewrite Ea', Es', Ew'. auto.
  - destruct (H2 t Ht) as (rg & G & Ea & Ew & Es). specialize (Hd t). rewrite G in Hd.
    destruct (mget M' t) as [rg'|]; [|contradiction]. destruct Hd as (Ea' & Es' & _ & Ew' & _). exists rg'. rewrite Ea', Es', Ew'. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma FMem_write (g : ghost) (rho : valuation) (cd : xcd) (M M' : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (t : int) (rg : region) (A A' : Z) :
  FMem g rho cd M nx m -> mget M t = Some rg -> rg_wr rg = true ->
  rbase rho t rg <= A -> A <= A' -> A' <= rbase rho t rg + to_Z (rg_size rg) ->
  munch [(A, A')] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  (forall x, A <= x < A' -> exists b, mrd bsegs m' (wa x) = Some b) ->
  same_dirs M M' -> ro_same M M' -> FMem g rho cd M' nx m'.
Proof.
  intros HF Eg Hw HA HAA HA' MU WM MI' HB Hd Hro.
  assert (WF : forall x, A <= x < A' -> aclient (rt_live RT (g_S g)) (rt_frames RT (g_S g)) B0 x /\ ~ caller_mem x /\ 0 <= x < 2 ^ 47).
  { intros x Hx. apply (wr_facts g rho cd M nx m t rg x HF Eg Hw). lia. }
  destruct HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & Hcnt & Hagr & Hsp0a).
  assert (OUT : forall a : word, ~ (A <= bv_unsigned a < A') -> m' a = m a).
  { intros a Ha. apply MU. cbn [outside]. split; [exact Ha | exact I]. }
  unfold FMem. cbv zeta.
  split; [rewrite (blk_list_same_dirs rho M M' _ Hd); exact Hlive|]. split; [exact Hfr|]. split; [exact Hnd|]. split; [exact Htl|].
  split; [exact (same_dirs_tags M M' nx Hd Htags)|]. split; [exact Hnx0|]. split; [exact Hnx|].
  split; [exact (same_dirs_class M M' _ _ Hd Hro Hcls)|]. split; [exact (same_dirs_link M M' _ _ Hd Hlink)|]. split; [exact Hrho|].
  split.
  { apply (af_frame RT AF (g_S g) m m' B0 HART ltac:(lia)); [|exact WM].
    intros a Hna. apply OUT. intros Hin. exact (Hna (proj1 (WF _ Hin))). }
  split; [exact MI'|].
  split.
  { destruct Hstk as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (S3 a Ha) as [Hwv (b & Hb)].
    split; [apply WM; exact Hwv|]. destruct (Z_lt_le_dec a A) as [L|L]; [|destruct (Z_lt_le_dec a A') as [L'|L']].
    - exists b. unfold mrd in *. rewrite OUT; [exact Hb|]. rewrite wa_unsigned by lia. lia.
    - apply HB. lia.
    - exists b. unfold mrd in *. rewrite OUT; [exact Hb|]. rewrite wa_unsigned by lia. lia. }
  split; [auto|]. split; [exact Hcnt|]. split; [|exact Hsp0a].
  intros a Hc. rewrite OUT; [exact (Hagr a Hc)|]. intros Hin. exact (proj1 (proj2 (WF _ Hin)) Hc).
Qed.

Lemma FMem_dirs (g : ghost) (rho : valuation) (cd : xcd) (M M' : HxMem.mem) (nx : int) (m : word -> option byte) :
  FMem g rho cd M nx m -> same_dirs M M' -> ro_same M M' -> FMem g rho cd M' nx m.
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrest) Hd Hro.
  unfold FMem. cbv zeta.
  split; [rewrite (blk_list_same_dirs rho M M' _ Hd); exact Hlive|]. split; [exact Hfr|]. split; [exact Hnd|]. split; [exact Htl|].
  split; [exact (same_dirs_tags M M' nx Hd Htags)|]. split; [exact Hnx0|]. split; [exact Hnx|].
  split; [exact (same_dirs_class M M' _ _ Hd Hro Hcls)|]. split; [exact (same_dirs_link M M' _ _ Hd Hlink) | exact Hrest].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem FInv_step : forall g rho cd, xstep_pres bsegs rho (FInv g rho cd).
Proof.
  intros g rho cd S S' ms ms' [HF (Hro & Hnf)] HRn HRn' Hst Ef Ec Eo Hd Hros Hm Hrs Enx Eabs.
  split; [|rewrite Eo; split; [exact Hro | exact (regs_nf_step _ _ Hnf Hrs)]].
  rewrite Enx. destruct Hm as [->|(t & rg & off & bs & Eg & Hw & Em & Hoff)]; [exact (FMem_dirs _ _ _ _ _ _ _ HF Hd Hros)|]. rewrite Em.
  pose proof (Rn_R bsegs rho S ms HRn) as (_ & _ & _ & _ & [HRg _]).
  pose proof (Rn_R bsegs rho S' ms' HRn') as (_ & _ & _ & _ & [HRg' _]).
  destruct (HRg t rg Eg) as (B0' & B1 & B2 & _ & _ & _ & _ & Hby).
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded (rg_size rg)) as Bs. unfold two63 in B1.
  set (A := rbase rho t rg + to_Z off) in *.
  assert (WR : wr_at bsegs (ms_mem ms) (rbase rho t rg) (to_Z (rg_size rg))).
  { split; [lia|]. split; [lia|]. intros i Hi. destruct (Hby i Hi) as (b & _ & _ & Hwv). exact (Hwv Hw). }
  eapply (FMem_write g rho cd (s_mem S) (s_mem S') (s_next S) (ms_mem ms) _ t rg A (A + Z.of_nat (length bs)) HF Eg Hw);
    try (unfold A; lia); try exact Hd; try exact Hros.
  - apply munch_write; [apply munch_refl| unfold A; lia| unfold A; lia|]. cbn [inside]. left. lia.
  - apply wmono_write. apply wmono_refl.
  - apply mem_inv_store; [destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmi & _); exact Hmi|].
    unfold A. apply (wr_at_store_ok bsegs (ms_mem ms) (rbase rho t rg) (to_Z (rg_size rg)) (to_Z off) (length bs) WR); lia.
  - intros x Hx. specialize (Hd t). rewrite Eg in Hd. destruct (mget (s_mem S') t) as [rg'|] eqn:Eg'; [|contradiction].
    destruct (HRg' t rg' Eg') as (_ & _ & _ & _ & _ & _ & _ & Hby').
    rewrite (rbase_same_dir rho t rg rg' Hd) in Hby'. destruct Hd as (_ & Es & _). rewrite Es in Hby'.
    destruct (Hby' (x - rbase rho t rg) ltac:(unfold A in Hx; lia)) as (b & Hb & _). exists b.
    replace (rbase rho t rg + (x - rbase rho t rg)) with x in Hb by lia. rewrite <- Em. exact Hb.
Qed.

End Inv.
