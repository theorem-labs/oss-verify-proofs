(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout ATacA PEnv LJ F_mm_A F_mm_D F_poison APrim F_prim_L0 AFrame ASec SecBits.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition sec_alloc_entry : Z := 0x37fb8.

Lemma munch_join : forall W1 W2 (m0 m m' : mem), munch W1 m0 m -> munch W2 m m' -> munch (W1 ++ W2) m0 m'.
Proof.
  intros W1 W2 m0 m m' M1 M2 x Hx. apply outside_app in Hx as [H1 H2]. rewrite (M2 x H2). exact (M1 x H1).
Qed.

Ltac lia1 :=
  first [ assumption
        | match goal with h : ~ (Z.le _ _ /\ Z.lt _ _) |- _ =>
            solve [ repeat match goal with h' : ~ (Z.le _ _ /\ Z.lt _ _) |- _ => lazymatch h' with h => fail | _ => clear h' end end; lia ] end
        | lia ].
Local Ltac dj_rec ::=
  first [ exact I | assumption
        | lazymatch goal with |- _ /\ _ => split; [dj_rec | dj_rec] end
        | lia
        | match goal with D : disjoint_from ?W ?A0 ?n0 |- disjoint_from ?W ?A ?n => apply (disjoint_from_sub W A0 n0 A n D); lia end ].
Local Ltac sub_fp_solve ::=
  unfold sub_fp; cbn [outside]; let xo := fresh "xo" in let Ho := fresh "Ho" in intros xo Ho; destruct_ands Ho;
  repeat split; lia1.

Local Ltac transport_after_call_fk segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_solve ]
            | lazymatch goal with FK : fkeep ?FI ?Wc ?st m m' |- _ =>
                apply (bytes_at_fkeep FI Wc st m m' A2 bs2) in H; [ | exact FK | solve_in_live | dj_solve ] end
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_solve ]
            | lazymatch goal with FK : fkeep ?FI ?Wc ?st m m' |- _ =>
                apply (rw_cells_fkeep FI Wc st m m' A2 cs2) in H; [ | exact FK | exact WM | solve_in_live | dj_solve ] end
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping stk hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>

      let J := fresh "MUj" in pose proof (munch_join Wq W mq m m' H MU) as J; clear H; rename J into H; cbn [List.app] in H
  | H : gmunch ?Wq ?mq m |- _ =>
      let J := fresh "GMj" in pose proof (gmunch_munch Wq W mq m m' H MU) as J; clear H; rename J into H; cbn [List.app] in H
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fk segs m m' MU WM.

Definition sec_clear (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => snd iv <= 0x10000 \/ 0x609000 <= fst iv \/ (707560 <= fst iv /\ snd iv <= 728454)) W.

Lemma poison_env_frame2 : forall E W m m',
  poison_env E m -> munch W m m' -> wmono asegs m m' -> sec_clear W -> poison_env E m'.
Proof.
  intros E W m m' PE MU WM F. unfold sec_clear in F. pe_split PE. unfold poison_env.
  repeat match goal with |- _ /\ _ => split end; try lia.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell C MU WM F end.
Qed.

Section TF.
Context {HC : HasCeiling}.
Definition thread_clear2 (L : athread) (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => (snd iv <= 0x10000 \/ 0x609000 <= fst iv \/ (707560 <= fst iv /\ snd iv <= 728454))
     /\ (at_ctx L + 160 <= fst iv \/ snd iv <= at_ctx L + 152)
     /\ (at_thr L + 24 <= fst iv \/ snd iv <= at_thr L + 8)
     /\ (at_thr L + 41 <= fst iv \/ snd iv <= at_thr L + 40)
     /\ (at_thr L + 3169 <= fst iv \/ snd iv <= at_thr L + 3168)) W.

#[using="Type"] Lemma thread_env_frame2 : forall L W m m',
  thread_env L m -> munch W m m' -> wmono asegs m m' -> thread_clear2 L W -> thread_env L m'.
Proof.
  intros L W m m' TE MU WM F. unfold thread_clear2 in F. te_split TE. unfold thread_env.
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell C MU WM F end.
Qed.
End TF.

Ltac hide h := lazymatch type of h with id _ => idtac | ?P => change (id P) in h end.
Ltac unhide h := lazymatch type of h with id ?P => change P in h | _ => idtac end.

Ltac fold_cb_load :=
  match goal with
  | |- context [sext 64 (bv_extract ?o ?w (le_bytes_to_word ?l))] =>
      let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract o w (le_bytes_to_word l)))) in
      replace (sext 64 (bv_extract o w (le_bytes_to_word l))) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [zext 64 (bv_extract ?o ?w (le_bytes_to_word ?l))] =>
      let v := eval vm_compute in (bv_unsigned (zext 64 (bv_extract o w (le_bytes_to_word l)))) in
      replace (zext 64 (bv_extract o w (le_bytes_to_word l))) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [bv_extract ?o ?w (le_bytes_to_word ?l)] =>
      let v := eval vm_compute in (bv_unsigned (bv_extract o w (le_bytes_to_word l))) in
      replace (bv_extract o w (le_bytes_to_word l)) with (Z_to_bv w v) by (vm_compute; reflexivity)
  end.

Lemma land_m8 x : 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros Hx.
  assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr'. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Lemma firstn_upd_snoc {X} : forall (ws : list X) (k : nat) (v : X) (l : list X),
  firstn k ws = l -> (k < length ws)%nat -> firstn (S k) (upd ws k v) = l ++ [v].
Proof.
  intros ws k v l Hf Hk. rewrite (upd_firstn_skipn ws k v Hk).
  rewrite firstn_app. rewrite firstn_all2 by (rewrite firstn_length; lia).
  rewrite firstn_length. replace (S k - Nat.min k (length ws))%nat with 1%nat by lia. cbn. rewrite Hf. reflexivity.
Qed.

Lemma chunks_sep_snoc : forall l d, chunks_sep l -> Forall (fun c => apart_chunks c d) l -> chunks_sep (l ++ [d]).
Proof.
  induction l as [|c l IH]; intros d Hs Hf; cbn.
  - constructor; [constructor| constructor].
  - inversion Hs; subst. inversion Hf; subst. constructor; [| apply IH; assumption].
    apply Forall_app. split; [assumption| constructor; [assumption| constructor]].
Qed.

Section RepHelpers.
Context {HC : HasCeiling}.
Variable AL : alayout.

#[using="Type"] Lemma hdrs_rep_gframe : forall S W m1 m2,
  hdrs_rep S m1 -> gmunch W m1 m2 -> wmono asegs m1 m2 ->
  Forall (fun c => disjoint_from W (sc_beg c) 32) (se_chunks S) -> hdrs_rep S m2.
Proof.
  intros S W m1 m2 HR G WM F i c Hi. pose proof (HR i c Hi) as R.
  eapply rw_cells_gtransport; [exact R| exact G| exact WM|]. cbn.
  apply (proj1 (Forall_forall _ _) F c). eapply nth_error_In; eauto.
Qed.

#[using="Type"] Lemma hdrs_rep_snoc : forall S d nres m,
  hdrs_rep S m -> rw_cells asegs m (sc_beg d) (hdr_cells d (se_n S)) ->
  hdrs_rep (mkSEC (se_chunks S ++ [d]) nres) m.
Proof.
  intros S d nres m HR HN i c Hi. cbn [se_chunks] in Hi.
  destruct (Nat.lt_ge_cases i (length (se_chunks S))) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hi by exact Hlt. exact (HR i c Hi).
  - rewrite nth_error_app2 in Hi by exact Hge.
    destruct (i - length (se_chunks S))%nat as [|k] eqn:E; cbn in Hi; [| destruct k; discriminate].
    injection Hi as <-. unfold se_n in HN. replace (Z.of_nat i) with (Z.of_nat (length (se_chunks S))) by lia. exact HN.
Qed.
End RepHelpers.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. cbn. repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]. Qed.

Lemma u64s_repeat_zero : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u64s]. rewrite le8_zero, IH.
  replace (8 * Datatypes.S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma u64arr_snoc_zeros : forall segs m A ws (n : nat),
  u64arr segs m A ws ->
  rw_cells segs m (A + 8 * Z.of_nat (length ws)) [CB (8 * n)%nat (repeat (Z_to_bv 8 0) (8 * n)%nat)] ->
  u64arr segs m A (ws ++ repeat (Z_to_bv 64 0) n).
Proof.
  intros segs m0 A ws n [B W] [[WF B2] W2]. split.
  - rewrite u64s_app, u64s_repeat_zero. apply bytes_at_app. split; [exact B|].
    rewrite u64s_length, Nat2Z.inj_mul. cbn [cells_bytes cbytes app] in B2. rewrite app_nil_r in B2. exact B2.
  - rewrite length_app, repeat_length, Nat2Z.inj_add, Z.mul_add_distr_l. apply wr_at_app; [lia|lia|]. split; [exact W|].
    cbn [cells_size csize Nat.add] in W2. rewrite Nat.add_0_r, Nat2Z.inj_mul in W2. exact W2.
Qed.

Ltac demod H z :=
  unfold id in H;
  lazymatch type of H with
  | ?a mod ?b = 0 => apply (proj1 (Z.mod_divide a b ltac:(lia))) in H; unfold Z.divide in H; destruct H as [z H]
  end.

Section SA.
Context {HC : HasCeiling}.
Variable E : penv.
Variable AL : alayout.
Notation L := (al_thread AL).
Notation PARR := (al_parr AL).

Definition sec_alloc_tree (S : asec) (size : Z) (avoid : list (Z * Z)) : itree nodeL (exc Z) :=
  ebind (t_anon (sec_msize size) avoid) (fun a =>
    ebind (if se_n S =? se_nres S then t_commit (PARR + 8 * se_nres S) K_PARR_STEP else Ret (Ok tt))
          (fun _ => Ret (Ok a))).

Definition sec_alloc_H (S : asec) (size a : Z) (H : word -> bool) : word -> bool :=
  let H1 := unhide_range (swlo a) (swhi a (sec_msize size)) (unhide_range a (a + sec_msize size) H) in
  if se_n S =? se_nres S
  then let p := PARR + 8 * se_nres S in unhide_range (swlo p) (swhi p K_PARR_STEP) (unhide_range p (p + K_PARR_STEP) H1)
  else H1.

Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (q lo size : Z) (m : word -> option byte) (H : word -> bool) (S : asec) (avoid : list (Z * Z)).

Notation MSZ := (sec_msize size).

Definition sec_alloc_W (a : Z) : list (Z * Z) :=
  [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
   (a, a + MSZ); (swlo a, swhi a MSZ); (swlo (PARR + 8 * se_nres S), swhi (PARR + 8 * se_nres S) K_PARR_STEP)].

Definition sec_alloc_Wg (a : Z) : list (Z * Z) :=
  [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
   (a, a + MSZ); (sh a, sh a + MSZ / 8)].

Definition sec_alloc_post : Z -> (word -> bool) -> machine_state -> Prop :=
  fun a H' ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (a + 4096)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = sec_alloc_H S size a H
    /\ munch [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
              (a, a + MSZ); (swlo a, swhi a MSZ); (swlo (PARR + 8 * se_nres S), swhi (PARR + 8 * se_nres S) K_PARR_STEP)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env L m' /\ RSEC AL (sec_alloc S a size) m'
    /\ (exists ts, rw_cells asegs m' (at_thr L + 2800) [CB 368 ts])
    /\ a mod 4096 = 0 /\ 0x609000 <= a /\ app_mem a MSZ /\ anon_place a MSZ
    /\ Forall (fun iv => a + MSZ <= fst iv \/ snd iv <= a) avoid
    /\ rw_cells asegs m' (a + 32) [CB (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))]
    /\ rw_cells asegs m' (a + 4096) [CB (Z.to_nat (MSZ - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (MSZ - 4096)))]
    /\ rw_cells asegs m' (sh a) [CB 512%nat (repeat (Z_to_bv 8 250) 512%nat)]
    /\ (exists j, rw_cells asegs m' (sh (a + 4096)) [CB (Z.to_nat (size / 8)) j])
    /\ rw_cells asegs m' (sh (a + 4096 + size)) [CB (Z.to_nat ((MSZ - 4096 - size) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((MSZ - 4096 - size) / 8)))]
    /\ shvis H' m'
    /\ gmunch [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
               (a, a + MSZ); (sh a, sh a + MSZ / 8)] m m'.

Definition sec_alloc_treeB (r : Z) : itree nodeL (exc Z) :=
  ebind (if se_n S =? se_nres S then t_commit (PARR + 8 * se_nres S) K_PARR_STEP else Ret (Ok tt)) (fun _ => Ret (Ok r)).
Definition sec_alloc_H1 (r : Z) : word -> bool := unhide_range (swlo r) (swhi r MSZ) (unhide_range r (r + MSZ) H).

#[using="Type"] Lemma sec_alloc_B : forall (r : Z) (mB : word -> option byte) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (junk8 : list byte) (ts : list byte) (Z8 K8 : Z),
  mem_inv asegs mB -> mclean (sec_alloc_H1 r) mB -> shvis (sec_alloc_H1 r) mB ->
  poison_env E mB -> thread_env L mB -> thread_layout_ok L -> alayout_ok AL ->
  sec_wf AL S -> sec_env AL mB -> sec_vars S mB -> parr_rep AL S mB -> hdrs_rep S mB ->
  rw_cells asegs mB (at_thr L + 2800) [CB 368 ts] ->
  stk asegs mB lo (q - 96) -> alloc_ceiling <= lo -> lo <= q - 688 -> q mod 16 = 0 -> q <= 2^47 ->
  rw_cells asegs mB (q - 96) [CB 8 junk8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (sec_alloc_W r) m mB -> gmunch (sec_alloc_Wg r) m mB -> wmono asegs m mB ->
  0 < size -> size mod 8 = 0 -> size <= 2^40 -> size = 8 * Z8 -> rup4k size = 8 * K8 ->
  r mod 4096 = 0 -> 0x609000 <= r -> anon_place r MSZ ->
  Forall (fun iv => r + MSZ <= fst iv \/ snd iv <= r) avoid ->
  Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL) ->
  Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks S) -> se_n S < K_MAX_CHUNKS ->
  rw_cells asegs mB r [CB (Z.to_nat MSZ) (repeat (Z_to_bv 8 0) (Z.to_nat MSZ))] ->
  rw_cells asegs mB (sh r) [CB 512%nat (repeat (Z_to_bv 8 250) 512%nat)] ->
  stk asegs mB (sh r + 512) (sh r + 512 + Z8) ->
  rw_cells asegs mB (sh (4096 + r + size)) [CB (Z.to_nat (K8 - Z8)) (repeat (Z_to_bv 8 250) (Z.to_nat (K8 - Z8)))] ->
  evt asegs (lzk (sec_alloc_H1 r) (sec_alloc_treeB r) sec_alloc_post)
    (MS (mkR (wz 0x380e0) (wz (q - 96)) gp (wz A0_TP) t0 t1 t2 (wz GSTATS) (wz SEC) (wz (4096 + r)) (wz 4096) a2 a3 a4 a5 a6 a7
             (wz MSZ) (wz size) (wz r) (wz r) (wz (MSZ + r)) (wz (4096 + r + size)) (wz 7) (wz (4096 + r))
             s10 s11 t3 t4 t5 t6)
        F (wz 0x38120) fc None mB (seg_rom asegs)).
Proof.
  intros until K8. intros MI C SV PE TE TL AO WF ENVS VARS PR HD TS STc CLO LOQ Q16 QHI FR MU GM WM S0 S8 S40 HZ8 HK8 PC1 PC2 PLACE PC5 AREG ACH WMAX PC6 POST0 USR POST1.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct ENVS as (ENV & ENV2 & ENV3). hide ENV2; hide ENV3. pose proof MI as MIB; hide MIB.
  pose proof WF as (W0 & W1 & W2 & W3 & W4 & W5 & W6). hide W1.
  pose proof TL as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11). hide T5; hide T6; hide T7; hide T8; hide T9; hide T10; hide T11.
  layout_facts AO 1%nat LPARR. layout_apart_fact AO 1%nat 2%nat LP2. layout_apart_fact AO 1%nat 3%nat LP3. hide LP2; hide LP3.
  destruct VARS as ((j24 & j32 & j40 & jsb & jpad & na & nf & cur & mx & VC) & (bsl & BSL & LBSL) & MTX & (g16 & g24 & GST)).
  destruct PR as (ws & PARRu & LWS & FWS). hide FWS. hide Q16.
  assert (MB : MSZ = rup4k size + 4096) by reflexivity.
  assert (ZK : 0 <= Z8 <= K8 /\ 8 * K8 < size + 4096 /\ size = 8 * Z8 /\ rup4k size = 8 * K8) by (pose proof (eq_refl (rup4k size)); unfold rup4k at 1 in H0; Z.div_mod_to_equations; nia).
  pose proof PLACE as [PC3' PCC]. pose proof (@alloc_ceiling_lt47 HC) as C47.
  assert (RLO : r + MSZ <= lo) by (clear - PCC CLO; lia).

  pose proof AREG as AREG'. unfold al_regions in AREG'.
  apply Forall_cons_iff in AREG' as [ASPACE AREG']. apply Forall_cons_iff in AREG' as [APARR AREG'].
  apply Forall_cons_iff in AREG' as [ACTX AREG']. apply Forall_cons_iff in AREG' as [ATHR AREG'].
  apply Forall_cons_iff in AREG' as [AFS AREG']. apply Forall_cons_iff in AREG' as [ADN AREG']. apply Forall_cons_iff in AREG' as [ASS AREG']. apply Forall_cons_iff in AREG' as [ADTLS _].
  cbn [fst snd] in ASPACE, APARR, ACTX, ATHR, AFS, ADN, ASS, ADTLS.
  assert (SHE : sh (r + MSZ) = sh r + 512 + K8) by (unfold sh; clear - ZK MB PC1 HZ8 HK8; Z.div_mod_to_equations; nia).
  assert (SHT : sh (4096 + r + size) = sh r + 512 + Z8) by (unfold sh; clear - ZK MB PC1 HZ8 HK8; Z.div_mod_to_equations; nia).
  pose proof (sw_range r MSZ PC2 ltac:(lia) ltac:(lia)) as SWR. pose proof (sw_bounds r MSZ PC2 ltac:(lia)) as (SW1 & SW2 & _ & _ & SW5 & _).
  assert (RSH : r + MSZ <= sh r \/ sh r + 512 + K8 <= r).
  { clear - PC3' SHE SW2 SWR. destruct PC3' as [[A B]|A]; [left; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; nia| right; lia]. }
  hide PC3'. hide PC1. hide RSH.

  unfold sec_alloc_W in MU. unfold sec_alloc_Wg in GM.
  pose proof (munch_refl [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23); (r, r + 32)] mB) as MUB.
  pose proof (gmunch_refl [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23); (r, r + 32)] mB) as GMB.
  pose proof (wmono_refl asegs mB) as WMB.
  expand_avoid. restore_avoid.
  match goal with A : r + MSZ <= PARR \/ _ |- _ => rename A into AVP end.
  match goal with A : r + MSZ <= at_ctx L \/ _ |- _ => rename A into AVC end.
  match goal with A : r + MSZ <= at_thr L \/ _ |- _ => rename A into AVT end.
  repeat match goal with A : r + MSZ <= _ \/ _ <= r |- _ => lazymatch A with AVP => fail | AVC => fail | AVT => fail | _ => clear A end end.
  hide AVP; hide AVC; hide AVT.

  clear Q16 T6 T7 T11 S8.
  demod PC1 rz. demod W1 wq.
  destruct LPARR as (P1 & P2 & P3 & P4 & P5 & P6 & P7). demod P3 pz.
  pose proof (conj P1 (conj P2 (conj P4 (conj P5 (conj P6 P7))))) as LPARR.
  replace (MSZ / 8) with (512 + K8) in GM by (clear - ZK MB; Z.div_mod_to_equations; nia).
  hide ASPACE; hide APARR; hide ACTX; hide ATHR; hide AFS; hide ADN; hide ASS; hide ADTLS.

  pose proof (rw_cells_split_CB asegs mB r [] (Z.to_nat MSZ) (repeat (Z_to_bv 8 0) (Z.to_nat MSZ)) [] [32%nat; Z.to_nat (MSZ - 32)] PC6 ltac:(cbn [sum_nat]; lia)) as PC6'.
  cbn [mk_CB_cells app] in PC6'.
  replace (Z.to_nat MSZ) with (32 + Z.to_nat (MSZ - 32))%nat in PC6' by lia.
  rewrite repeat_app in PC6'. rewrite firstn_app, skipn_app in PC6'.
  rewrite !repeat_length, !Nat.sub_diag in PC6'. cbn [firstn skipn app] in PC6'. rewrite app_nil_r in PC6'.
  change (skipn 0 ?l) with l in PC6'. rewrite firstn_all2 in PC6' by (rewrite repeat_length; lia).
  pose proof (proj1 (rw_cells_app asegs mB r [CB 32 (repeat (Z_to_bv 8 0) 32)] _) PC6') as [HDR BLK].
  cbn [cells_size csize Nat.add] in BLK. replace (r + Z.of_nat 32) with (r + 32) in BLK by lia.
  replace (firstn (Z.to_nat (MSZ - 32)) (skipn 32 (repeat (Z_to_bv 8 0) 32) ++ repeat (Z_to_bv 8 0) (Z.to_nat (MSZ - 32))))
     with (repeat (Z_to_bv 8 0) (Z.to_nat (MSZ - 32))) in BLK
     by (change (skipn 32 (repeat (Z_to_bv 8 0) 32)) with (@nil byte); cbn [app]; symmetry; apply firstn_all2; rewrite repeat_length; lia).
  clear PC6 PC6'. cbn [repeat] in HDR.
  hide BLK; hide POST0; hide POST1; hide USR; hide TS; hide PARRu.
  pose proof (munch_refl [(r, r + 24)] mB) as MUh. pose proof (wmono_refl asegs mB) as WMh.
  do 3 zstep.
  unhide TS; unhide PARRu.
  lazymatch type of MUh with munch ?Wt ?ma ?mb =>
    apply (rw_cells_transport asegs Wt ma mb) in TS; [| exact MUh| exact WMh| unhide AVT; clear - AVT MB ZK; cbn [disjoint_from]; simpl_sizes; lia];
    apply (u64arr_transport asegs Wt ma mb) in PARRu; [| exact MUh| exact WMh| unhide AVP; clear - AVP MB ZK LWS W0 W2; cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; lia] end.
  clear MUh WMh.
  zstep. if_false_z.
  do 4 zstep.
  unfold b8 in MTX.
  amo_step.   try fold_cb_load.
  do 4 zstep.
  amo_step.
  zstep. if_false.
  zstep.
  zstep. if_false.
  do 2 zstep.
  assert (WN : 0 <= se_n S) by (unfold se_n; lia).
  rewrite ?(Z.mod_small (se_n S)) by lia. rewrite (Z.shiftr_div_pow2 (se_n S) 20), (Z.div_small (se_n S)) by lia.
  zstep. if_false.

  do 8 zstep.
  do 8 zstep.
  do 8 zstep.
  do 8 zstep.
  do 8 zstep.
  do 2 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (?e ≫ 56)] => change e with (clz_swar (smear64 MSZ)) end.
  pose proof (Z.log2_spec MSZ ltac:(lia)) as [LG1 LG2]. rewrite <- Z.add_1_r in LG2. pose proof (Z.log2_nonneg MSZ) as LG0.
  assert (LG3 : Z.log2 MSZ < 47) by (apply (proj1 (Z.log2_lt_pow2 MSZ 47 ltac:(lia))); change (2 ^ 47) with 140737488355328; lia).
  rewrite (clz_swar_smear (Z.log2 MSZ) MSZ) by lia.

  zstep. if_cases KE; zify_cond KE.
  2: {
  pose proof W0 as NR16.
  zstep.
  zstep.   rewrite lxor63_small by lia. replace (63 - (63 - Z.log2 MSZ)) with (Z.log2 MSZ) by lia.
  hide TS; hide PARRu.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(r, r + 32)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.
  zstep.
  unhide TS; unhide PARRu.
  lazymatch type of MUh with munch ?Wt ?ma ?mb =>
    apply (rw_cells_transport asegs Wt ma mb) in TS; [| exact MUh| exact WMh| unhide AVT; clear - AVT MB ZK; cbn [disjoint_from]; simpl_sizes; lia];
    apply (u64arr_transport asegs Wt ma mb) in PARRu; [| exact MUh| exact WMh| unhide AVP; clear - AVP MB ZK LWS W0 W2; cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; lia] end.
  clear MUh WMh.
  do 2 zstep.
  rewrite (Z.shiftl_mul_pow2 (se_n S) 3) by lia. change (2 ^ 3) with 8.
  pose proof (u64arr_store_ok asegs _ PARR ws (se_n S) (wa (PARR + 8 * se_n S)) PARRu ltac:(lia) eq_refl) as SOK.
  replace (PARR + se_n S * 8) with (PARR + 8 * se_n S) by lia.
  unhide AVP; unhide LP3.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
    pose proof (u64arr_write asegs mx PARR ws (se_n S) (wz r) PARRu ltac:(lia)) as PARRu2 end.
  clear PARRu SOK. store_done. rename PARRu2 into PARRu.
  hide AVP; hide LP3.
  do 6 zstep.
  zstep.   sstep.
  do 2 zstep.
  zstep.

  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
  all: cycle 1. 1: zstep.   all: cycle 1.
  all: do 2 zstep.
  all: destruct (nth_error bsl (Z.to_nat (Z.log2 MSZ))) as [wb|] eqn:NB; [| exfalso; apply nth_error_None in NB; lia].
  all: pose proof (u64arr_read asegs _ SEC_BSL bsl (Z.log2 MSZ) wb (wa (SEC_BSL + 8 * Z.log2 MSZ)) BSL NB ltac:(lia) eq_refl) as HRB.
  all: rewrite (Z.shiftl_mul_pow2 (Z.log2 MSZ) 3) by lia; change (2 ^ 3) with 8; replace (724760 + Z.log2 MSZ * 8) with (724760 + 8 * Z.log2 MSZ) by lia.
  all: zstep.
  all: do 2 zstep.
  all: pose proof (u64arr_store_ok asegs _ SEC_BSL bsl (Z.log2 MSZ) (wa (SEC_BSL + 8 * Z.log2 MSZ)) BSL ltac:(rewrite LBSL; lia) eq_refl) as SOKB.
  all: zstep.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ ?v) _) =>
    lazymatch v with le8 ?w => pose proof (u64arr_write asegs mx SEC_BSL bsl (Z.log2 MSZ) w BSL ltac:(rewrite LBSL; lia)) as BSL2 end end.
  all: clear BSL SOKB HRB; store_done; rename BSL2 into BSL.
  all: zstep.
  all: amo_step.
  all: zstep.
  all: amo_step.
  all: zstep.
  all: lazymatch type of MTX with rw_cells _ ?mm _ _ =>
    assert (MTX' : rw_cells asegs mm SEC_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]])
      by (destruct MTX as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
          lazymatch goal with |- bytes_at _ _ _ ?l => replace l with (cells_bytes [C4 (Z_to_bv 64 1)]); [exact Hb|] end;
          cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]);
    clear MTX end.
  all: sstep.
  all: do 11 zstep.
  all: zstep.
  all: zstep.
  all: release_frame FR STc q.
  all: unfold sec_alloc_treeB; rewrite (proj2 (Z.eqb_neq (se_n S) (se_nres S))) by lia.
  all: change (ebind (Ret (Ok tt)) (fun _ : unit => Ret (Ok r))) with (Ret (Ok r) : itree nodeL (exc Z)).
  all: lz_ret.

  all: restore_avoid.
  all: assert (PC1' : r mod 4096 = 0) by (rewrite PC1; apply Z_mod_mult); clear PC1; rename PC1' into PC1; hide PC1.
  all: assert (W1' : se_nres S mod 16384 = 0) by (rewrite W1; apply Z_mod_mult); clear W1; rename W1' into W1; hide W1.
  all: try rename SWR0 into SWP.
  all: try (pose proof (sw_range (PARR + 8 * se_nres S) 131072 ltac:(lia) ltac:(lia) ltac:(lia)) as SWP).
  all: replace (q - 96 + 96) with q by lia; replace (4096 + r) with (r + 4096) by lia.
  all: unhide BLK; unhide POST0; unhide POST1; unhide USR; unhide RSH; unhide MIB; unhide ENV2; unhide ENV3.

  all: pose proof (rw_cells_gtransport _ _ _ _ _ BLK GMB WMB ltac:(unhide AVT; unhide AVP; clear - AVT AVP RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as BLK'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ POST0 GMB WMB ltac:(clear - RSH SHE SW1 SW2 SWR RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as POST0'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ POST1 GMB WMB ltac:(clear - RSH SHE SHT SW1 SW2 SWR RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as POST1'.
  all: pose proof (stk_gtransport _ _ _ _ _ USR GMB WMB ltac:(clear - RSH SHE SW1 SW2 SWR RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; repeat split; lia)) as USR'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ ENV2 GMB WMB ltac:(clear - CLO LOQ ACR T3 LPARR PC2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as ENV2'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ ENV3 GMB WMB ltac:(clear - CLO LOQ ACR T3 LPARR PC2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as ENV3'.
  all: clear BLK POST0 POST1 USR ENV2 ENV3.

  all: lazymatch type of BLK' with rw_cells _ ?mm _ _ =>
    pose proof (rw_cells_split_CB asegs mm (r + 32) [] (Z.to_nat (MSZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (MSZ - 32))) [] [Z.to_nat 4064; Z.to_nat (MSZ - 4096)] BLK' ltac:(cbn [sum_nat]; lia)) as BLK2 end.
  all: cbn [mk_CB_cells app] in BLK2.
  all: replace (Z.to_nat (MSZ - 32)) with (Z.to_nat 4064 + Z.to_nat (MSZ - 4096))%nat in BLK2 by lia.
  all: rewrite repeat_app, firstn_app, skipn_app, !repeat_length, !Nat.sub_diag in BLK2.
  all: replace (firstn (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))) with (repeat (Z_to_bv 8 0) (Z.to_nat 4064)) in BLK2 by (symmetry; apply firstn_all2; rewrite repeat_length; lia).
  all: replace (skipn (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))) with (@nil byte) in BLK2 by (symmetry; apply skipn_all2; rewrite repeat_length; lia).
  all: cbn [firstn skipn app] in BLK2; rewrite app_nil_r in BLK2.
  all: change (skipn 0 ?l) with l in BLK2.
  all: rewrite firstn_all2 in BLK2 by (rewrite repeat_length; lia).
  all: pose proof (proj1 (rw_cells_app asegs _ (r + 32) [CB (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))] _) BLK2) as [BLKa BLKb];
       cbn [cells_size csize Nat.add] in BLKb; replace (r + 32 + Z.of_nat (Z.to_nat 4064 + 0)) with (r + 4096) in BLKb by lia; clear BLK2 BLK'.

  all: edestruct (stk_carve asegs _ (sh r + 512) (sh r + 512 + Z8) (Z.to_nat Z8) USR') as [_ [ju USRC]]; [rewrite Z2Nat.id by lia; lia|];
       rewrite Z2Nat.id in USRC by lia; replace (sh r + 512 + Z8 - Z8) with (sh (r + 4096)) in USRC by (unhide PC1; unfold sh; clear - PC1; Z.div_mod_to_equations; nia);
       replace (Z.to_nat Z8) with (Z.to_nat (size / 8)) in USRC by (clear - ZK; f_equal; Z.div_mod_to_equations; nia).
  all: replace (4096 + r + size) with (r + 4096 + size) in POST1' by lia;
       replace (Z.to_nat (K8 - Z8)) with (Z.to_nat ((MSZ - 4096 - size) / 8)) in POST1' by (clear - ZK MB; f_equal; Z.div_mod_to_equations; nia).
  all: unfold sec_alloc_post; finish.
  all: try (eexists; exact TS).
  all: try (eexists; exact USRC).
  all: try lazymatch goal with |- _ = sec_alloc_H _ _ _ _ => unfold sec_alloc_H1, sec_alloc_H; first [rewrite (proj2 (Z.eqb_neq (se_n S) (se_nres S))) by lia | rewrite (proj2 (Z.eqb_eq (se_n S) (se_nres S))) by lia]; reflexivity end.
  all: try lazymatch goal with |- mem_inv _ ?mf =>
         intros xa b Hb; destruct (ro_addr asegs xa) eqn:RO; [| reflexivity]; exfalso;
         assert (XL : 0x10000 <= bv_unsigned xa < 0xaa000) by (destruct (Z_lt_le_dec (bv_unsigned xa) 0x10000); [rewrite a0_ro_addr_false in RO; [discriminate| lia]|]; destruct (Z_lt_le_dec (bv_unsigned xa) 0xaa000); [lia|]; rewrite a0_ro_addr_false in RO; [discriminate| lia]);
         rewrite (MUB xa) in Hb by (cbn [outside]; repeat split; lia);
         rewrite (MIB xa b Hb) in RO; discriminate end.
  all: try lazymatch goal with |- poison_env _ _ =>
         eapply (poison_env_frame2 E _ mB _ PE MUB WMB);
         clear - LOQ CLO ACR T3 T4 LPARR PC2 SWR SWP W0 W2 NR16; unfold sec_clear; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia end.
  all: try lazymatch goal with |- thread_env _ _ =>
         eapply (thread_env_frame2 L _ mB _ TE MUB WMB);
         unhide AVC; unhide AVT; unhide T5; unhide LP2; unhide LP3;
         clear - AVC AVT RLO CLO LOQ QHI T1 T2 T3 T4 T5 LP2 LP3 SWR SWP SW1 SW2 SHE ZK MB PC2 PCC LPARR W0 W2 NR16;
         unfold thread_clear2; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia end.
  all: try lazymatch goal with |- shvis _ _ => first [ eapply shvis_wmono; [exact SVx| exact WM2] | eapply shvis_wmono; [exact SV| exact WMB] ] end.
  all: try (apply anon_place_app_mem; exact PLACE).
  all: try lazymatch goal with |- gmunch _ _ _ => unfold sec_alloc_Wg; replace (MSZ / 8) with (512 + K8) by (clear - ZK MB; Z.div_mod_to_equations; nia); exact GM end.
  all: lazymatch goal with |- RSEC _ _ _ => idtac end.

  all: unfold RSEC; split; [| split; [| split; [| split]]].
  all: try lazymatch goal with |- sec_wf _ _ =>
       unhide W1; unfold sec_wf, sec_alloc, se_n in *; cbn [se_chunks se_nres];
       first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia]; rewrite length_app; cbn [length];
       split; [lia|]; split; [first [exact W1 | rewrite <- Zplus_mod_idemp_l, W1; reflexivity]|]; split; [lia|]; split; [lia|]; split; [lia|]; split;
       [ apply Forall_app; split; [exact W5|]; constructor; [| constructor];
         unfold chunk_ok; cbn [sc_beg sc_msize sc_size]; unhide PC1;
         split; [exact PC1|]; split; [lia|]; split; [lia|]; split; [reflexivity|]; split; [exact PC3'|]; split; [exact PCC|];
         unfold al_regions; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold apart; expand_avoid; restore_avoid; assumption
       | apply chunks_sep_snoc; [exact W6|]; eapply Forall_impl; [| exact ACH]; cbv beta; intros c Hin; unfold apart_chunks; cbn [sc_beg sc_msize];
         pose proof (proj1 (Forall_forall _ _) PC5 _ Hin) as X; cbn [fst snd] in X; lia ] end.
  all: try lazymatch goal with |- sec_env _ _ => split; [exact ENV| split; [exact ENV2'| exact ENV3']] end.
  all: try lazymatch goal with |- sec_vars _ _ => unfold sec_vars; split; [| split; [| split]];
       [ exists j24, j32, j40; eexists _, jpad, _, nf, _, _;
         unfold se_n, sec_alloc; cbn [se_chunks se_nres]; first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia];
         rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; fold (se_n S); exact VC
       | eexists; split; [exact BSL| rewrite upd_length; exact LBSL]
       | lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
           destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
           lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
           cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end
       | eexists _, _; match goal with G0 : rw_cells asegs _ 725400 _ |- _ => exact G0 end ] end.
  all: try lazymatch goal with |- parr_rep _ _ _ =>
       eexists; split; [exact PARRu|]; unfold sec_alloc, se_n in *; cbn [se_chunks se_nres];
       first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia]; rewrite ?upd_length; split; [first [exact LWS | rewrite ?length_app; cbn; lia] |];
       rewrite length_app; cbn [length]; rewrite Nat.add_1_r, Nat2Z.id, map_app; cbn [map sc_beg];
       unhide FWS; apply firstn_upd_snoc; [exact FWS| lia] end.
  all: try lazymatch goal with |- hdrs_rep _ _ => apply hdrs_rep_snoc;
       [ eapply (hdrs_rep_gframe S _ mB _ HD GMB WMB);
         apply Forall_forall; intros c Hc;
         pose proof (proj1 (Forall_forall _ _) W5 c Hc) as CK; unfold chunk_ok in CK; destruct CK as (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7);
         unfold al_regions in CK7; apply Forall_cons_iff in CK7 as [_ CK7]; apply Forall_cons_iff in CK7 as [CP CK7]; apply Forall_cons_iff in CK7 as [_ CK7]; apply Forall_cons_iff in CK7 as [CT _];
         cbn [fst snd] in CP, CT; unfold apart in CP, CT;
         pose proof (proj1 (Forall_forall _ _) PC5 _ (proj1 (Forall_forall _ _) ACH c Hc)) as CR; cbn [fst snd] in CR;
         assert (CM : 32 <= sc_msize c) by (rewrite CK4; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia);
         clear - CK2 CK5 CK6 CP CT CR CM CLO LOQ ACR T3 LPARR PC2 SWR SWP SW1 SW2 RSH MB ZK SHE;
         cbn [disjoint_from]; repeat split; lia
       | unfold hdr_cells; cbn [sc_beg sc_msize sc_size]; exact HDR ] end.

  all: unfold sec_vars; split; [| split; [| split]].
  all: try (exists j24, j32, j40; eexists _, jpad, _, nf, _, _;
         unfold se_n, sec_alloc; cbn [se_chunks se_nres]; first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia];
         rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; fold (se_n S); exact VC).
  all: try (eexists; split; [exact BSL| rewrite upd_length; exact LBSL]).
  all: try lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
           destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
           lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
           cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end.
  all: try (eexists _, _; match goal with G0 : rw_cells asegs _ 725400 _ |- _ => exact G0 end).
  }

  assert (NR16 : se_nres S + 16384 <= 1048576) by (unhide W1; clear - W1 WMAX KE W0; Z.div_mod_to_equations; lia).
  zstep.
  do 3 zstep.
  rewrite (Z.shiftl_mul_pow2 (se_n S) 3) by lia. change (2 ^ 3) with 8.
  do 4 zstep.
  replace (se_n S * 8 + PARR) with (PARR + 8 * se_nres S) by lia.
  zstep.
  unfold sec_alloc_treeB. rewrite (proj2 (Z.eqb_eq (se_n S) (se_nres S))) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (poison_env_frame2 E _ mB mm PE MUB WMB ltac:(clear - LOQ CLO ACR T3 T4 LPARR PC2 SWR; unfold sec_clear; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia)) as PEc;
    pose proof (shvis_wmono _ mB mm SV WMB) as SVc end.
  assert (APM : app_mem (PARR + 8 * se_nres S) K_PARR_STEP) by (clear - P1 P4 P5 P6 W0 W2 NR16 KE; unfold app_mem in *; lia).

  hide HDR; hide PARRu; hide TS; hide STc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (gmunch_refl [(q - 96 - 368, q - 96); (PARR + 8 * se_nres S, PARR + 8 * se_nres S + K_PARR_STEP)] mm) as GX;
    pose proof (wmono_refl asegs mm) as WX end.
  callA (rar_mapordie_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 96) lo (PARR + 8 * se_nres S) K_PARR_STEP);
    [ assumption | assumption | exact SVc | exact PEc | exact STc
    | clear - CLO ACR; lia | clear - LOQ; lia | clear - QHI; lia
    | reflexivity | reflexivity
    | clear - P3 W1; rewrite P3, W1; replace (pz * 4096 + 8 * (wq * 16384)) with ((pz + 32 * wq) * 4096) by lia; apply Z_mod_mult
    | reflexivity
    | clear - P4 W0; lia | lia | clear - P5 W2 NR16 W0; lia | exact APM
    | left; clear - P2 CLO W2 NR16 W0; lia | ].
  clear STc PEc SVc APM. rename PC into STc. rename PC0 into PEx. rename PC3 into ZNEW. clear PC4. rename PC6 into SVx.
  destruct SWB as (SB1 & SB2 & _ & _ & SB5 & _). lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.

  unhide HDR; unhide PARRu; unhide TS.
  pose proof (rw_cells_gtransport _ _ _ _ _ HDR GX WX ltac:(unhide AVP; clear - AVP RLO LOQ MB ZK NR16 KE W0; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as HDR'.
  pose proof (u64arr_gtransport _ _ _ _ _ PARRu GX WX ltac:(clear - P2 CLO LOQ W2 W0 LWS; cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; repeat split; lia)) as PARRu'.
  pose proof (rw_cells_gtransport _ _ _ _ _ TS GX WX ltac:(unhide LP3; clear - LP3 T4 CLO LOQ NR16 KE W0; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as TS'.
  clear HDR PARRu TS GX WX. rename HDR' into HDR. rename PARRu' into PARRu. rename TS' into TS.

  replace (Z.to_nat 131072) with (8 * Z.to_nat 16384)%nat in ZNEW by (change 8%nat with (Z.to_nat 8); rewrite <- Z2Nat.inj_mul by lia; reflexivity).
  replace (PARR + 8 * se_nres S) with (PARR + 8 * Z.of_nat (length ws)) in ZNEW by (clear - LWS; lia).
  pose proof (u64arr_snoc_zeros asegs _ PARR ws (Z.to_nat 16384) PARRu ZNEW) as PARRu2.
  assert (LWS2 : Z.of_nat (length (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat 16384))) = se_nres S + 16384)
    by (rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by lia; clear - LWS; lia).
  assert (FWS2 : firstn (length (se_chunks S)) (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat 16384)) = map (fun c => Z_to_bv 64 (sc_beg c)) (se_chunks S)).
  { unhide FWS. rewrite firstn_app. replace (length (se_chunks S) - length ws)%nat with 0%nat by (unfold se_n in KE; clear - KE LWS; lia).
    cbn [firstn]. rewrite app_nil_r. exact FWS. }
  clear PARRu ZNEW FWS LWS. remember (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat 16384)) as ws2 eqn:Hws2. clear Hws2 ws.
  rename PARRu2 into PARRu. rename LWS2 into LWS. rename FWS2 into FWS. rename ws2 into ws. hide FWS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (wmono_refl asegs mm) as WM2 end.
  zstep.
  do 2 zstep.
  do 2 zstep.
  zstep.
  zstep.
  zstep.
  zstep.   rewrite lxor63_small by lia. replace (63 - (63 - Z.log2 MSZ)) with (Z.log2 MSZ) by lia.
  hide TS; hide PARRu.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(r, r + 32)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.
  zstep.
  unhide TS; unhide PARRu.
  lazymatch type of MUh with munch ?Wt ?ma ?mb =>
    apply (rw_cells_transport asegs Wt ma mb) in TS; [| exact MUh| exact WMh| unhide AVT; clear - AVT MB ZK; cbn [disjoint_from]; simpl_sizes; lia];
    apply (u64arr_transport asegs Wt ma mb) in PARRu; [| exact MUh| exact WMh| unhide AVP; clear - AVP MB ZK LWS W0 W2 NR16; cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; lia] end.
  clear MUh WMh.
  do 2 zstep.
  rewrite (Z.shiftl_mul_pow2 (se_n S) 3) by lia. change (2 ^ 3) with 8.
  pose proof (u64arr_store_ok asegs _ PARR ws (se_n S) (wa (PARR + 8 * se_n S)) PARRu ltac:(lia) eq_refl) as SOK.
  replace (PARR + se_n S * 8) with (PARR + 8 * se_n S) by lia.
  unhide AVP; unhide LP3.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
    pose proof (u64arr_write asegs mx PARR ws (se_n S) (wz r) PARRu ltac:(lia)) as PARRu2 end.
  clear PARRu SOK. store_done. rename PARRu2 into PARRu.
  hide AVP; hide LP3.
  do 6 zstep.
  zstep.   sstep.
  do 2 zstep.
  zstep.

  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
  all: cycle 1. 1: zstep.   all: cycle 1.
  all: do 2 zstep.
  all: destruct (nth_error bsl (Z.to_nat (Z.log2 MSZ))) as [wb|] eqn:NB; [| exfalso; apply nth_error_None in NB; lia].
  all: pose proof (u64arr_read asegs _ SEC_BSL bsl (Z.log2 MSZ) wb (wa (SEC_BSL + 8 * Z.log2 MSZ)) BSL NB ltac:(lia) eq_refl) as HRB.
  all: rewrite (Z.shiftl_mul_pow2 (Z.log2 MSZ) 3) by lia; change (2 ^ 3) with 8; replace (724760 + Z.log2 MSZ * 8) with (724760 + 8 * Z.log2 MSZ) by lia.
  all: zstep.
  all: do 2 zstep.
  all: pose proof (u64arr_store_ok asegs _ SEC_BSL bsl (Z.log2 MSZ) (wa (SEC_BSL + 8 * Z.log2 MSZ)) BSL ltac:(rewrite LBSL; lia) eq_refl) as SOKB.
  all: zstep.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ ?v) _) =>
    lazymatch v with le8 ?w => pose proof (u64arr_write asegs mx SEC_BSL bsl (Z.log2 MSZ) w BSL ltac:(rewrite LBSL; lia)) as BSL2 end end.
  all: clear BSL SOKB HRB; store_done; rename BSL2 into BSL.
  all: zstep.
  all: amo_step.
  all: zstep.
  all: amo_step.
  all: zstep.
  all: lazymatch type of MTX with rw_cells _ ?mm _ _ =>
    assert (MTX' : rw_cells asegs mm SEC_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]])
      by (destruct MTX as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
          lazymatch goal with |- bytes_at _ _ _ ?l => replace l with (cells_bytes [C4 (Z_to_bv 64 1)]); [exact Hb|] end;
          cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]);
    clear MTX end.
  all: sstep.
  all: do 11 zstep.
  all: zstep.
  all: zstep.
  all: release_frame FR STc q.
  all: lz_ret.

  all: restore_avoid.
  all: assert (PC1' : r mod 4096 = 0) by (rewrite PC1; apply Z_mod_mult); clear PC1; rename PC1' into PC1; hide PC1.
  all: assert (W1' : se_nres S mod 16384 = 0) by (rewrite W1; apply Z_mod_mult); clear W1; rename W1' into W1; hide W1.
  all: try rename SWR0 into SWP.
  all: try (pose proof (sw_range (PARR + 8 * se_nres S) 131072 ltac:(lia) ltac:(lia) ltac:(lia)) as SWP).
  all: replace (q - 96 + 96) with q by lia; replace (4096 + r) with (r + 4096) by lia.
  all: unhide BLK; unhide POST0; unhide POST1; unhide USR; unhide RSH; unhide MIB; unhide ENV2; unhide ENV3.

  all: pose proof (rw_cells_gtransport _ _ _ _ _ BLK GMB WMB ltac:(unhide AVT; unhide AVP; clear - AVT AVP RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as BLK'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ POST0 GMB WMB ltac:(clear - RSH SHE SW1 SW2 SWR RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as POST0'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ POST1 GMB WMB ltac:(clear - RSH SHE SHT SW1 SW2 SWR RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as POST1'.
  all: pose proof (stk_gtransport _ _ _ _ _ USR GMB WMB ltac:(clear - RSH SHE SW1 SW2 SWR RLO CLO LOQ T3 LPARR PC2 MB ZK W0 W2; cbn [disjoint_from]; repeat split; lia)) as USR'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ ENV2 GMB WMB ltac:(clear - CLO LOQ ACR T3 LPARR PC2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as ENV2'.
  all: pose proof (rw_cells_gtransport _ _ _ _ _ ENV3 GMB WMB ltac:(clear - CLO LOQ ACR T3 LPARR PC2; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as ENV3'.
  all: clear BLK POST0 POST1 USR ENV2 ENV3.

  all: lazymatch type of BLK' with rw_cells _ ?mm _ _ =>
    pose proof (rw_cells_split_CB asegs mm (r + 32) [] (Z.to_nat (MSZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (MSZ - 32))) [] [Z.to_nat 4064; Z.to_nat (MSZ - 4096)] BLK' ltac:(cbn [sum_nat]; lia)) as BLK2 end.
  all: cbn [mk_CB_cells app] in BLK2.
  all: replace (Z.to_nat (MSZ - 32)) with (Z.to_nat 4064 + Z.to_nat (MSZ - 4096))%nat in BLK2 by lia.
  all: rewrite repeat_app, firstn_app, skipn_app, !repeat_length, !Nat.sub_diag in BLK2.
  all: replace (firstn (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))) with (repeat (Z_to_bv 8 0) (Z.to_nat 4064)) in BLK2 by (symmetry; apply firstn_all2; rewrite repeat_length; lia).
  all: replace (skipn (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))) with (@nil byte) in BLK2 by (symmetry; apply skipn_all2; rewrite repeat_length; lia).
  all: cbn [firstn skipn app] in BLK2; rewrite app_nil_r in BLK2.
  all: change (skipn 0 ?l) with l in BLK2.
  all: rewrite firstn_all2 in BLK2 by (rewrite repeat_length; lia).
  all: pose proof (proj1 (rw_cells_app asegs _ (r + 32) [CB (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))] _) BLK2) as [BLKa BLKb];
       cbn [cells_size csize Nat.add] in BLKb; replace (r + 32 + Z.of_nat (Z.to_nat 4064 + 0)) with (r + 4096) in BLKb by lia; clear BLK2 BLK'.

  all: edestruct (stk_carve asegs _ (sh r + 512) (sh r + 512 + Z8) (Z.to_nat Z8) USR') as [_ [ju USRC]]; [rewrite Z2Nat.id by lia; lia|];
       rewrite Z2Nat.id in USRC by lia; replace (sh r + 512 + Z8 - Z8) with (sh (r + 4096)) in USRC by (unhide PC1; unfold sh; clear - PC1; Z.div_mod_to_equations; nia);
       replace (Z.to_nat Z8) with (Z.to_nat (size / 8)) in USRC by (clear - ZK; f_equal; Z.div_mod_to_equations; nia).
  all: replace (4096 + r + size) with (r + 4096 + size) in POST1' by lia;
       replace (Z.to_nat (K8 - Z8)) with (Z.to_nat ((MSZ - 4096 - size) / 8)) in POST1' by (clear - ZK MB; f_equal; Z.div_mod_to_equations; nia).
  all: unfold sec_alloc_post; finish.
  all: try (eexists; exact TS).
  all: try (eexists; exact USRC).
  all: try lazymatch goal with |- _ = sec_alloc_H _ _ _ _ => unfold sec_alloc_H1, sec_alloc_H; first [rewrite (proj2 (Z.eqb_neq (se_n S) (se_nres S))) by lia | rewrite (proj2 (Z.eqb_eq (se_n S) (se_nres S))) by lia]; reflexivity end.
  all: try lazymatch goal with |- mem_inv _ ?mf =>
         intros xa b Hb; destruct (ro_addr asegs xa) eqn:RO; [| reflexivity]; exfalso;
         assert (XL : 0x10000 <= bv_unsigned xa < 0xaa000) by (destruct (Z_lt_le_dec (bv_unsigned xa) 0x10000); [rewrite a0_ro_addr_false in RO; [discriminate| lia]|]; destruct (Z_lt_le_dec (bv_unsigned xa) 0xaa000); [lia|]; rewrite a0_ro_addr_false in RO; [discriminate| lia]);
         rewrite (MUB xa) in Hb by (cbn [outside]; repeat split; lia);
         rewrite (MIB xa b Hb) in RO; discriminate end.
  all: try lazymatch goal with |- poison_env _ _ =>
         eapply (poison_env_frame2 E _ mB _ PE MUB WMB);
         clear - LOQ CLO ACR T3 T4 LPARR PC2 SWR SWP W0 W2 NR16; unfold sec_clear; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia end.
  all: try lazymatch goal with |- thread_env _ _ =>
         eapply (thread_env_frame2 L _ mB _ TE MUB WMB);
         unhide AVC; unhide AVT; unhide T5; unhide LP2; unhide LP3;
         clear - AVC AVT RLO CLO LOQ QHI T1 T2 T3 T4 T5 LP2 LP3 SWR SWP SW1 SW2 SHE ZK MB PC2 PCC LPARR W0 W2 NR16;
         unfold thread_clear2; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia end.
  all: try lazymatch goal with |- shvis _ _ => first [ eapply shvis_wmono; [exact SVx| exact WM2] | eapply shvis_wmono; [exact SV| exact WMB] ] end.
  all: try (apply anon_place_app_mem; exact PLACE).
  all: try lazymatch goal with |- gmunch _ _ _ => unfold sec_alloc_Wg; replace (MSZ / 8) with (512 + K8) by (clear - ZK MB; Z.div_mod_to_equations; nia); exact GM end.
  all: lazymatch goal with |- RSEC _ _ _ => idtac end.

  all: unfold RSEC; split; [| split; [| split; [| split]]].
  all: try lazymatch goal with |- sec_wf _ _ =>
       unhide W1; unfold sec_wf, sec_alloc, se_n in *; cbn [se_chunks se_nres];
       first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia]; rewrite length_app; cbn [length];
       split; [lia|]; split; [first [exact W1 | rewrite <- Zplus_mod_idemp_l, W1; reflexivity]|]; split; [lia|]; split; [lia|]; split; [lia|]; split;
       [ apply Forall_app; split; [exact W5|]; constructor; [| constructor];
         unfold chunk_ok; cbn [sc_beg sc_msize sc_size]; unhide PC1;
         split; [exact PC1|]; split; [lia|]; split; [lia|]; split; [reflexivity|]; split; [exact PC3'|]; split; [exact PCC|];
         unfold al_regions; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold apart; expand_avoid; restore_avoid; assumption
       | apply chunks_sep_snoc; [exact W6|]; eapply Forall_impl; [| exact ACH]; cbv beta; intros c Hin; unfold apart_chunks; cbn [sc_beg sc_msize];
         pose proof (proj1 (Forall_forall _ _) PC5 _ Hin) as X; cbn [fst snd] in X; lia ] end.
  all: try lazymatch goal with |- sec_env _ _ => split; [exact ENV| split; [exact ENV2'| exact ENV3']] end.
  all: try lazymatch goal with |- sec_vars _ _ => unfold sec_vars; split; [| split; [| split]];
       [ exists j24, j32, j40; eexists _, jpad, _, nf, _, _;
         unfold se_n, sec_alloc; cbn [se_chunks se_nres]; first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia];
         rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; fold (se_n S); exact VC
       | eexists; split; [exact BSL| rewrite upd_length; exact LBSL]
       | lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
           destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
           lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
           cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end
       | eexists _, _; match goal with G0 : rw_cells asegs _ 725400 _ |- _ => exact G0 end ] end.
  all: try lazymatch goal with |- parr_rep _ _ _ =>
       eexists; split; [exact PARRu|]; unfold sec_alloc, se_n in *; cbn [se_chunks se_nres];
       first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia]; rewrite ?upd_length; split; [first [exact LWS | rewrite ?length_app; cbn; lia] |];
       rewrite length_app; cbn [length]; rewrite Nat.add_1_r, Nat2Z.id, map_app; cbn [map sc_beg];
       unhide FWS; apply firstn_upd_snoc; [exact FWS| lia] end.
  all: try lazymatch goal with |- hdrs_rep _ _ => apply hdrs_rep_snoc;
       [ eapply (hdrs_rep_gframe S _ mB _ HD GMB WMB);
         apply Forall_forall; intros c Hc;
         pose proof (proj1 (Forall_forall _ _) W5 c Hc) as CK; unfold chunk_ok in CK; destruct CK as (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7);
         unfold al_regions in CK7; apply Forall_cons_iff in CK7 as [_ CK7]; apply Forall_cons_iff in CK7 as [CP CK7]; apply Forall_cons_iff in CK7 as [_ CK7]; apply Forall_cons_iff in CK7 as [CT _];
         cbn [fst snd] in CP, CT; unfold apart in CP, CT;
         pose proof (proj1 (Forall_forall _ _) PC5 _ (proj1 (Forall_forall _ _) ACH c Hc)) as CR; cbn [fst snd] in CR;
         assert (CM : 32 <= sc_msize c) by (rewrite CK4; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia);
         clear - CK2 CK5 CK6 CP CT CR CM CLO LOQ ACR T3 LPARR PC2 SWR SWP SW1 SW2 RSH MB ZK SHE;
         cbn [disjoint_from]; repeat split; lia
       | unfold hdr_cells; cbn [sc_beg sc_msize sc_size]; exact HDR ] end.

  all: unfold sec_vars; split; [| split; [| split]].
  all: try (exists j24, j32, j40; eexists _, jpad, _, nf, _, _;
         unfold se_n, sec_alloc; cbn [se_chunks se_nres]; first [rewrite (proj2 (Z.eqb_neq _ _)) by lia | rewrite (proj2 (Z.eqb_eq _ _)) by lia];
         rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; fold (se_n S); exact VC).
  all: try (eexists; split; [exact BSL| rewrite upd_length; exact LBSL]).
  all: try lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
           destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
           lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
           cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end.
  all: try (eexists _, _; match goal with G0 : rw_cells asegs _ 725400 _ |- _ => exact G0 end).
Qed.

#[using="Type"] Lemma sec_allocate_spec : forall (x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word) (ts : list byte) (alo ahi : Z),
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env L m -> thread_layout_ok L -> alayout_ok AL ->
  RSEC AL S m -> rw_cells asegs m (at_thr L + 2800) [CB 368 ts] ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 688 -> q mod 16 = 0 -> q <= 2^47 ->
  a0 = wz SEC -> a1 = wz GSTATS -> a2 = wz size -> a3 = wz 8 ->
  0 < size -> size mod 8 = 0 -> size <= 2^40 ->
  In (alo, ahi) avoid -> alo <= lo -> q <= ahi ->
  Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL) ->
  Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks S) -> se_n S < K_MAX_CHUNKS ->
  implA H (sec_alloc_tree S size avoid) sec_alloc_post
        (MS (mkR ra (wz q) gp (wz A0_TP) x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz sec_alloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until ahi. intros MI C SV PE TE TL AO RS TS ST CLO LOQ Q16 QHI -> -> -> -> S0 S8 S40 AIN ALO AHI AREG ACH WMAX.
  unfold sec_alloc_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct RS as (WF & (ENV & ENV2 & ENV3) & VARS & PR & HD).
  pose proof WF as (W0 & W1 & W2 & W3 & W4 & W5 & W6). clear W1.
  pose proof TL as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11). hide T5. clear T6 T7 T11. hide T8; hide T9; hide T10.
  layout_apart_fact AO 1%nat 2%nat LP2. layout_apart_fact AO 1%nat 3%nat LP3. hide LP2; hide LP3.
  destruct VARS as ((j24 & j32 & j40 & jsb & jpad & na & nf & cur & mx & VC) & (bsl & BSL & LBSL) & MTX & (g16 & g24 & GST)).
  destruct PR as (ws & PARRu & LWS & FWS). hide FWS.
  pose proof (munch_refl [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23)] m) as MU.
  pose proof (gmunch_refl [(q - 688, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23)] m) as GM.
  pose proof (wmono_refl asegs m) as WM.
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & P3 & P4 & P5 & P6 & P7). demod P3 pz.
  pose proof (conj P1 (conj P2 (conj P4 (conj P5 (conj P6 P7))))) as LPARR.

  pose proof AREG as AREG'. unfold al_regions in AREG'.
  apply Forall_cons_iff in AREG' as [ASPACE AREG']. apply Forall_cons_iff in AREG' as [APARR AREG'].
  apply Forall_cons_iff in AREG' as [ACTX AREG']. apply Forall_cons_iff in AREG' as [ATHR AREG'].
  apply Forall_cons_iff in AREG' as [AFS AREG']. apply Forall_cons_iff in AREG' as [ADN AREG']. apply Forall_cons_iff in AREG' as [ASS AREG']. apply Forall_cons_iff in AREG' as [ADTLS _].
  cbn [fst snd] in ASPACE, APARR, ACTX, ATHR, AFS, ADN, ASS, ADTLS.

  hide ASPACE; hide AFS; hide ADN; hide ASS; hide ADTLS.
  assert (RUP1 : size <= rup4k size < size + 4096) by (unfold rup4k; Z.div_mod_to_equations; nia).
  assert (RUP2 : exists u, rup4k size = u * 4096) by (unfold rup4k; eexists; reflexivity). destruct RUP2 as [ru RUP2].
  assert (MB : MSZ = rup4k size + 4096) by reflexivity.
  assert (ZK' : exists Z8 K8, 0 <= Z8 <= K8 /\ size = 8 * Z8 /\ rup4k size = 8 * K8 /\ 8 * K8 < size + 4096).
  { exists (size / 8), (rup4k size / 8). clear - S0 S8 RUP1 RUP2. Z.div_mod_to_equations; nia. }
  destruct ZK' as (Z8 & K8 & ZK). clear S8.
  demod Q16 qz.
  hide ENV2; hide ENV3.
  carve_frame 96%nat ST.
  lz_go. do 12 zstep.
  do 3 zstep.   zstep. if_false.
  zstep. zstep.
  do 2 zstep. zstep. if_false.
  do 5 zstep.
  rewrite land_m4096 by lia.
  do 5 zstep.
  replace (size + 4095 - (size + 4095) mod 4096) with (rup4k size) by (unfold rup4k; clear - S0; Z.div_mod_to_equations; nia).
  change (Z.land ((0 - Z.b2z (4096 <? 8)) mod 18446744073709551616) 8) with 0.
  replace (rup4k size + 4096 + 0) with MSZ by (unfold sec_msize; lia). change (rup4k size + 4096) with MSZ.
  zstep. if_true_z.
  unhide ENV2; unhide ENV3.
  pose proof (rw_cells_transport asegs _ m _ _ _ ENV2 MU WM ltac:(cbn; lia)) as ENV2c.
  pose proof (rw_cells_transport asegs _ m _ _ _ ENV3 MU WM ltac:(cbn; lia)) as ENV3c. hide ENV2; hide ENV3.
  do 4 zstep.
  clear ENV2c ENV3c.
  zstep. zstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (poison_env_frame2 E _ m mm PE MU WM ltac:(clear - LOQ CLO ACR T3 T4 LPARR; unfold sec_clear; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia)) as PEc;
    pose proof (shvis_wmono _ m mm SV WM) as SVc;
    pose proof (gmunch_refl [(q - 96 - 320, q - 96)] mm) as GX; pose proof (wmono_refl asegs mm) as WX end.
  hide PARRu; hide TS; hide FR; hide AIN; hide APARR; hide ACTX; hide ATHR.
  callA (mmap_or_die_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 96) lo MSZ alo ahi avoid);
    [ assumption | assumption | exact SVc | exact PEc | replace (q - 96) with (q + -96) by lia; exact ST
    | clear - CLO ACR; lia | clear - LOQ; lia | clear - QHI; lia
    | reflexivity
    | rewrite MB, RUP2; replace (ru * 4096 + 4096) with ((ru + 1) * 4096) by lia; apply Z_mod_mult
    | clear - S0 S40 RUP1 MB; lia | exact AIN | exact ALO | clear - AHI; lia | ].
  clear PEc SVc. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  rename PC into STc. rename PC0 into PEc. rename PC3 into AM. pose proof PC4 as PLACE. destruct PC4 as [PC3' PCC]. hide PC3'.
  demod PC1 rz.
  pose proof (@alloc_ceiling_lt47 HC) as C47.
  assert (RLO : r + MSZ <= lo) by (clear - PCC CLO; lia).
  pose proof (sw_range r MSZ PC2 ltac:(clear - S0 RUP1 MB; lia) ltac:(clear - PCC C47; lia)) as SWR.
  pose proof (sw_bounds r MSZ PC2 ltac:(clear - S0 RUP1 MB; lia)) as (SW1 & SW2 & _ & _ & SW5 & _).
  assert (SHE : sh (r + MSZ) = sh r + 512 + K8) by (unfold sh; clear - ZK MB PC1; Z.div_mod_to_equations; nia).
  assert (SHT : sh (4096 + r + size) = sh r + 512 + Z8) by (unfold sh; clear - ZK MB PC1; Z.div_mod_to_equations; nia).
  assert (RSH : r + MSZ <= sh r \/ sh r + 512 + K8 <= r).
  { unhide PC3'. clear - PC3' SHE SW2 SWR. destruct PC3' as [[A B]|A]; [left; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; nia| right; lia]. }
  hide RSH.

  restore_avoid.
  pose proof (proj1 (Forall_forall _ _) PC5 _ AIN) as AVS. pose proof (proj1 (Forall_forall _ _) PC5 _ APARR) as AVP.
  pose proof (proj1 (Forall_forall _ _) PC5 _ ACTX) as AVC. pose proof (proj1 (Forall_forall _ _) PC5 _ ATHR) as AVT.
  cbn [fst snd] in AVS, AVP, AVC, AVT.

  unhide FR; unhide PARRu; unhide TS.
  pose proof (rw_cells_gtransport _ _ _ _ _ FR GX WX ltac:(clear - AVS ALO AHI CLO LOQ RLO MB ZK; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as FR'.
  pose proof (u64arr_gtransport _ _ _ _ _ PARRu GX WX ltac:(clear - AVP P2 CLO LOQ W0 W2 LWS MB ZK; cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; repeat split; lia)) as PARRu'.
  pose proof (rw_cells_gtransport _ _ _ _ _ TS GX WX ltac:(clear - AVT T4 CLO LOQ MB ZK; cbn [disjoint_from]; simpl_sizes; repeat split; lia)) as TS'.
  clear FR PARRu TS GX WX. rename FR' into FR. rename PARRu' into PARRu. rename TS' into TS.
  pose proof (wmono_refl asegs m1) as WMg.
  hide AVS; hide AVP; hide AVC; hide AVT.
  zstep. if_false_z.
  zstep. zstep.
  do 2 zstep.
  replace (Z.land 4095 r) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; clear - PC1 PC2; Z.div_mod_to_equations; nia).
  zstep. if_false.
  do 3 zstep.
  replace (Z.land (4096 + r) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - PC1 PC2; Z.div_mod_to_equations; nia).
  do 5 zstep.
  change (Z.land ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) 8) with 0. rewrite !Z.add_0_l.
  do 4 zstep.
  rewrite !land_m8 by lia.
  replace (4096 + r + size - (4096 + r + size) mod 8) with (4096 + r + size) by (clear - ZK PC1 PC2; Z.div_mod_to_equations; nia).
  replace (4096 + r + 7 - (4096 + r + 7) mod 8) with (4096 + r) by (clear - PC1 PC2; Z.div_mod_to_equations; nia).
  do 4 zstep.
  replace (4096 + r - r) with 4096 by lia.

  edestruct (stk_split asegs _ (swlo r) (sh r + 512) (swhi r MSZ) PC7) as [WS1 WS2]; [clear - SW1 SW2 SHE ZK; lia|].
  edestruct (stk_carve asegs _ (swlo r) (sh r + 512) 512 WS1) as [_ [jh SHH]]; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SW1; lia|].
  change (Z.of_nat 512) with 512 in SHH. replace (sh r + 512 - 512) with (sh r) in SHH by lia. clear WS1 PC7.
  assert (SHP : sh r + 512 + K8 <= PARR \/ PARR + 2^23 <= sh r) by (clear - P1 SWR SW1 SW2 SHE; lia).
  assert (ABh : r mod 8 = 0 /\ 4096 mod 8 = 0 /\ 0 <= 4096 /\ poison_range r 4096 /\ 0 <= 250 < 256)
    by (unhide PC3'; clear - PC1 PC3' PCC C47 MB ZK RUP1; unfold poison_range; Z.div_mod_to_equations; nia).
  unhide RSH. hide STc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      call (poison_shadow_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 96) lo r 4096 250 mm MIx ltac:(clear - CLO ACR LOQ QHI; lia) ABh _ _ _ _ _ jh);
      [exact PEc| exact STc| left; lia| exact SHH|] end end.
  clear PEc ABh STc. match goal with P : poison_env E ?mm, Q : stk asegs ?mm lo _ |- _ => rename P into PEc; rename Q into STc end.
  change (4096 / 8) with 512 in *.
  rename POST into POST0.
  do 4 zstep.
  replace (MSZ + r - (4096 + r + size)) with (rup4k size - size) by lia.
  edestruct (stk_split asegs _ (sh r + 512) (sh r + 512 + Z8) (swhi r MSZ) WS2) as [WSU WS3]; [clear - ZK SW2 SHE; lia|].
  edestruct (stk_split asegs _ (sh r + 512 + Z8) (sh r + 512 + K8) (swhi r MSZ) WS3) as [WST WS4]; [clear - ZK SW2 SHE; lia|].
  edestruct (stk_carve asegs _ (sh r + 512 + Z8) (sh r + 512 + K8) (Z.to_nat (K8 - Z8)) WST) as [_ [jt SHT']]; [rewrite Z2Nat.id by lia; lia|].
  rewrite Z2Nat.id in SHT' by lia. replace (sh r + 512 + K8 - (K8 - Z8)) with (sh (4096 + r + size)) in SHT' by lia.
  clear WST WS3 WS2 WS4. rename WSU into USR.
  assert (ED : (rup4k size - size) / 8 = K8 - Z8) by (clear - ZK; Z.div_mod_to_equations; nia).
  assert (ABt : (4096 + r + size) mod 8 = 0 /\ (rup4k size - size) mod 8 = 0 /\ 0 <= rup4k size - size
                /\ poison_range (4096 + r + size) (rup4k size - size) /\ 0 <= 250 < 256)
    by (unhide PC3'; clear - PC1 PC3' PCC C47 MB ZK RUP1 S0; unfold poison_range; split; [Z.div_mod_to_equations; nia|]; split; [Z.div_mod_to_equations; nia|]; lia).
  rewrite <- ED in SHT'. hide STc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      call (poison_shadow_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 96) lo (4096 + r + size) (rup4k size - size) 250 mm MIx
              ltac:(clear - CLO ACR LOQ QHI; lia) ABt _ _ _ _ _ jt);
      [exact PEc| exact STc| left; lia| exact SHT'|] end end.
  clear PEc ABt STc. match goal with P : poison_env E ?mm, Q : stk asegs ?mm lo _ |- _ => rename P into PEc; rename Q into STc end.
  rewrite ED in *. clear ED. rename POST into POST1. hide RSH.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (thread_env_frame2 L _ m mm TE MU WM ltac:(unhide AVC; unhide AVT; unhide T5; unhide LP2; unhide LP3; clear - AVC AVT RLO CLO LOQ QHI T1 T2 T3 T4 T5 LP2 LP3 SWR SW1 SW2 SHE SHT ZK MB PC2 PCC LPARR;
                                                       unfold thread_clear2; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia)) as TEc end.
  zstep.   hide STc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      call (gcts_spec L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 96) mm lo _ _);
      [exact STc| exact CLO| clear - LOQ; lia| clear - Q16; rewrite Q16; replace (qz * 16 - 96) with ((qz - 6) * 16) by lia; apply Z_mod_mult| clear - QHI; lia| exact TEc| exact TL| exact MIx|] end end.
  clear TEc STc. match goal with P : thread_env L ?mm, Q : stk asegs ?mm lo _ |- _ => rename P into TEc; rename Q into STc end.

  do 3 zstep.
  replace (Z.land (4096 + r) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - PC1 PC2; Z.div_mod_to_equations; nia).
  do 2 zstep.

  hide PC6; hide PARRu.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(at_thr L + 2872, at_thr L + 2888)] mm) as MUt; pose proof (wmono_refl asegs mm) as WMt end.
  do 2 zstep.
  unhide PC6; unhide PARRu.
  lazymatch type of MUt with munch ?Wt ?ma ?mb =>
    apply (rw_cells_transport asegs Wt ma mb) in PC6; [| exact MUt| exact WMt| unhide AVT; clear - AVT MB ZK; cbn [disjoint_from]; simpl_sizes; lia];
    apply (u64arr_transport asegs Wt ma mb) in PARRu; [| exact MUt| exact WMt| unhide LP3; clear - LP3 LWS W2 W0; cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; lia] end.
  clear MUt WMt.
  zstep. if_false.
  zstep. zstep.
  do 2 zstep.
  replace (Z.land 4095 (4096 + r)) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; clear - PC1 PC2; Z.div_mod_to_equations; nia).
  zstep. if_false.
  zstep. if_false_z.
  zstep. if_false_z.
  zstep.
  replace (4096 + r - 4096) with r by lia.

  destruct (rw_cells_forget _ _ _ _ TS) as [ts' TS']. cbn [cells_size csize Nat.add] in TS'. clear TS.
  replace (q + -96) with (q - 96) in FR by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (poison_env_frame2 E _ m mm PE MU WM ltac:(clear - LOQ CLO ACR T3 T4 LPARR PC2 SWR SW1 SW2 SHE SHT ZK MB RLO; unfold sec_clear; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia)) as PEf;
    pose proof (thread_env_frame2 L _ m mm TE MU WM ltac:(unhide AVC; unhide AVT; unhide T5; unhide LP2; unhide LP3; clear - AVC AVT RLO CLO LOQ QHI T1 T2 T3 T4 T5 LP2 LP3 SWR SW1 SW2 SHE SHT ZK MB PC2 PCC LPARR;
                                                       unfold thread_clear2; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia)) as TEf;
    unhide ENV2; unhide ENV3;
    pose proof (rw_cells_transport asegs _ m mm _ _ ENV2 MU WM ltac:(clear - LOQ CLO ACR T3 PC2 SWR SW1 SW2 SHE SHT ZK MB P1; cbn; lia)) as ENV2f;
    pose proof (rw_cells_transport asegs _ m mm _ _ ENV3 MU WM ltac:(clear - LOQ CLO ACR T3 PC2 SWR SW1 SW2 SHE SHT ZK MB P1; cbn; lia)) as ENV3f end.
  clear PEc TEc.
  lz_here. eapply implA_go_clean; [exact MC|].
  eapply sec_alloc_B;
    [ assumption | exact MC | | exact PEf | exact TEf | exact TL | exact AO | exact WF
    | split; [exact ENV| split; [exact ENV2f| exact ENV3f]]
    | split; [exists j24, j32, j40, jsb, jpad, na, nf, cur, mx; exact VC| split; [exists bsl; split; [exact BSL| exact LBSL]| split; [exact MTX| exists g16, g24; exact GST]]]
    | exists ws; split; [exact PARRu| split; [exact LWS| exact FWS]]
    | | exact TS' | exact STc | exact CLO | exact LOQ
    | rewrite Q16; apply Z_mod_mult | exact QHI | exact FR
    | | | exact WM | exact S0
    | clear - ZK; destruct ZK as (_ & E0 & _); rewrite E0, Z.mul_comm; apply Z_mod_mult
    | exact S40 | clear - ZK; destruct ZK as (_ & E0 & E1 & _); exact E0 | clear - ZK; destruct ZK as (_ & E0 & E1 & _); exact E1
    | rewrite PC1; apply Z_mod_mult | exact PC2 | exact PLACE | exact PC5 | exact AREG | exact ACH | exact WMAX
    | exact PC6 | exact POST0 | exact USR | exact POST1 ].
  all: try lazymatch goal with |- munch _ _ _ => unfold sec_alloc_W; refine (munch_weaken _ _ _ _ _ MU); clear - SW1 SW2 SHE SHT ZK MB LOQ; sub_fp_solve end.
  all: try lazymatch goal with |- gmunch _ _ _ => unfold sec_alloc_Wg; refine (gmunch_weaken _ _ _ _ _ GM); clear - SW1 SW2 SHE SHT ZK MB LOQ; sub_fp_solve end.
  all: try lazymatch goal with |- hdrs_rep _ _ =>
    eapply (hdrs_rep_gframe S _ m _ HD GM WM);
    apply Forall_forall; intros c Hc;
    pose proof (proj1 (Forall_forall _ _) W5 c Hc) as CK; unfold chunk_ok in CK; destruct CK as (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7);
    unfold al_regions in CK7; apply Forall_cons_iff in CK7 as [_ CK7]; apply Forall_cons_iff in CK7 as [CP CK7]; apply Forall_cons_iff in CK7 as [_ CK7]; apply Forall_cons_iff in CK7 as [CT _];
    cbn [fst snd] in CP, CT; unfold apart in CP, CT;
    pose proof (proj1 (Forall_forall _ _) PC5 _ (proj1 (Forall_forall _ _) ACH c Hc)) as CR; cbn [fst snd] in CR;
    assert (CM : 32 <= sc_msize c) by (rewrite CK4; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia);
    clear - CK2 CK5 CK6 CP CT CR CM CLO LOQ ACR T3 LPARR PC2 SWR SW1 SW2 MB ZK SHE SHT;
    cbn [disjoint_from]; repeat split; lia end.
  all: try lazymatch goal with |- shvis _ _ => eapply shvis_wmono; [exact PC8| exact WMg] end.
Qed.
End SA.
