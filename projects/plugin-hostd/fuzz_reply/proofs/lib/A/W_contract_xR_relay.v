(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_contract_x.v; 60 of its 201 lines of code are new or changed and 1871 lines of the source are left out. *)
(* Contract texts of lib/A/W_contract_x.v at a world relation R, for relay_remove (rr_post_x :905, rr_spec_x :924) and
   relay_instance_gone (rig_post_x :948, rig_spec_x :975).  A beside-file of W_contract_xR.v (a Theorem Labs lane's) and
   W_contract_srlf_xR.v, written in their form: R is a Section variable right after ARx, with its laws R_refl, R_trans,
   WLE_R (the definitions use none of them), and the SAME R is in the post journal (W_journal_x.ajournal_gx_xR) and in
   the step relation (YA0nH.SRrG SEGS R).  Both functions free (relay_remove at +0x1b0, relay_instance_gone at +0x288,
   through CTX_AFREE), so at the cf instance R := wle' SEGS RZ_cf.
   Against the strict texts only these change: the name, `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST
   ARx R`, `SRr SEGS` -> `SRrG SEGS R`, the post name X_post_x -> X_post_xR.  The comments inside the strict texts are
   left out.  Section s6R's variables are Section s6's (W_contract_x.v:884-898) with R after ARx.
   Instances: at R := wle each R text IS its strict text (X_x_wle, by conversion); the R text at wle gives the strict
   one (X_x_of_xR); a strict text gives the R text at every R that contains wle (X_xR_of_x, from WLE_R).
   Owner: a Theorem Labs lane (a7's ruling, 2026-10-31).  The walks pb_relay_remove_xR / pb_relay_instance_gone_xR are not here.
   proves no function (kind: statement text; contract twins, no walk). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_kit W_journal W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_c relay_remove_b_c relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_b_c RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListTr HarnessTr RelayRunF.
(* the import block above is W_contract_x.v's (lines 42-77), so every name of the texts resolves as there *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section s6R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Variable CTX_AFREE : list (list Z).
(* W_contract_x.v:905 rr_post_x at R *)
Definition rr_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
    (G0 FD : Z) (es : list rentry) (j : nat) (h : hsrc) (c : ctl) (O : list byte) (mx cap out : Z)
    (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
  ajournal_gx_xR SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
  aregs_preserved regs regs' /\ apres_kept B W mem W' mem' /\
  mo_le MT S S' (tr_cost MT (rr_tr c mx (Z.of_nat (length O)) cap FD es h)) /\
  rp_RM RP S' kr /\
  alock_at RG W' mem' false /\ awake_at RG W' mem' /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (rr_drains FD es = true -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept W mem W' mem' a) /\
  ((FD < 0 \/ forall e, In e es -> re_fd e <> FD) ->
   arelay_at B RG ly' S' W' mem' G0 es /\ aout_at B RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
   Permutation (ablocks B ly' S') (ablocks B ly S)) /\
  (forall i, (i < length es)%nat -> 0 <= FD -> re_fd (nth i es relay_remove_b_c.no_entry) = FD ->
   rr_found B RG ly S W mem ly' S' W' mem' G0 es i j h c O mx cap out).
(* W_contract_x.v:924 rr_spec_x at R *)
Definition rr_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch (G0 FD : Z) (es : list rentry) (j : nat) (h : hsrc) (c : ctl) (O : list byte) (mx cap out : Z),
let tr := rr_tr c mx (Z.of_nat (length O)) cap FD es h in
afn_pre_x SEGS B ARx RR_STK_x ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 -> count_cid 0 (frames S) < fs_frames 0 -> rg_place B RG ->
getr regs 10 = w64 FD -> - 2 ^ 31 <= FD < 2 ^ 31 ->
alock_at RG W mem false -> awake_at RG W mem ->
arelay_at B RG ly S W mem G0 es ->
aout_at B RG ly S W mem c O mx (Z.of_nat (length O)) cap out -> rom_view SEGS W mem ->
(forall i, (i < length es)%nat -> re_fd (nth i es relay_remove_b_c.no_entry) = FD ->
 re_eof (nth i es relay_remove_b_c.no_entry) = 0 -> dr_src_ok B RG ly S W mem (nth i es relay_remove_b_c.no_entry) h j) ->
(exists rest, Permutation (ablocks B ly S)
  ((G0, ATABLE) :: concat (map aentry_blks es) ++ (if rr_drains FD es then asrc_blks h else []) ++ aout_blks cap out ++ rest)) ->
tr_max tr < MMAX -> blocks_bytes S + tr_peak tr <= LIVE_MAX -> mo_ok MT S (tr_cost MT tr) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (tr_cost MT_rk tr) + kr) ->
cnt_ok_pk RP (rr_pk tr) (ablocks B ly S) ->
spZ regs + 16 < ly_top ly -> In (pc + 436 :: raZ regs :: spine ch) CTX_AFREE ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (rr_post_xR regs ly S Hp W mem md G0 FD es j h c O mx cap out kr).
(* W_contract_x.v:948 rig_post_x at R *)
Definition rig_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
    (G0 ID : Z) (es : list rentry) (hs : list (hsrc * nat)) (c : ctl) (O : list byte) (mx cap out : Z)
    (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k (qs : list (rentry * hsrc)) (c2 : ctl) (O2 : list byte) (cap2 out2 : Z) rest,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
  ajournal_gx_xR SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
  aregs_preserved regs regs' /\ apres_kept B W mem W' mem' /\
  mo_le MT S S' (tr_cost MT (rig_tr c mx (Z.of_nat (length O)) cap ID es hs)) /\
  rp_RM RP S' kr /\
  alock_at RG W' mem' false /\
  rig_rel (relay_instance_gone_b_c.instance_prefix ID) mx c O cap (combine es hs) qs c2 O2 cap2 /\
  length qs = length es /\
  arelay_at B RG ly' S' W' mem' G0 (map fst qs) /\
  aout_at B RG ly' S' W' mem' c2 O2 mx (Z.of_nat (length O2)) cap2 out2 /\
  (forall i, (i < length es)%nat -> re_eof (nth i es relay_remove_b_c.no_entry) = 0 ->
   asrc_at B ly' S' W' mem' (rg_s RG + ASRC * Z.of_nat (snd (nth i hs relay_instance_gone_b_c.no_hj)))
     (snd (nth i qs (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (forall j, In j (rig_slots (combine es hs)) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept W mem W' mem' a) /\
  Permutation (ablocks B ly S)
    ((G0, ATABLE) :: concat (map aentry_blks es) ++ rig_srcs (combine es hs) ++ aout_blks cap out ++ rest) /\
  Permutation (ablocks B ly' S')
    ((G0, ATABLE) :: concat (map aentry_blks (map fst qs)) ++
     concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else []) (combine (combine es hs) qs)) ++
     aout_blks cap2 out2 ++ rest).
(* W_contract_x.v:975 rig_spec_x at R *)
Definition rig_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch (G0 ID : Z) (es : list rentry) (hs : list (hsrc * nat)) (c : ctl) (O : list byte) (mx cap out : Z),
let tr := rig_tr c mx (Z.of_nat (length O)) cap ID es hs in
afn_pre_x SEGS B ARx RIG_STK_x ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 -> count_cid 1 (frames S) < fs_frames 1 -> rg_place B RG ->
getr regs 10 = w64 ID -> - 2 ^ 31 <= ID < 2 ^ 31 ->
alock_at RG W mem false ->
arelay_at B RG ly S W mem G0 es ->
aout_at B RG ly S W mem c O mx (Z.of_nat (length O)) cap out -> rom_view SEGS W mem ->
length hs = length es ->
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly S W mem (fst p) (fst (snd p)) (snd (snd p))) (combine es hs) ->
NoDup (rig_slots (combine es hs)) ->
(exists rest, Permutation (ablocks B ly S)
  ((G0, ATABLE) :: concat (map aentry_blks es) ++ rig_srcs (combine es hs) ++ aout_blks cap out ++ rest)) ->
tr_max tr < MMAX -> blocks_bytes S + tr_peak tr <= LIVE_MAX -> mo_ok MT S (tr_cost MT tr) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (tr_cost MT_rk tr) + kr) ->
cnt_ok_pk RP (rig_pk tr) (ablocks B ly S) ->
spZ regs + 16 < ly_top ly -> In (pc + 652 :: raZ regs :: spine ch) CTX_AFREE ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (rig_post_xR regs ly S Hp W mem md G0 ID es hs c O mx cap out kr).
End s6R.

Section s6Ri.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Variable CTX_AFREE : list (list Z).
Lemma rr_post_x_wle : rr_post_x B PST ARx MT RP RG = rr_post_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma rr_spec_x_wle : rr_spec_x B PST ARx MT RP MMAX RG CTX_AFREE = rr_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG CTX_AFREE.
Proof. reflexivity. Qed.
Lemma rr_spec_x_of_xR : forall pc,
  rr_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG CTX_AFREE pc -> rr_spec_x B PST ARx MT RP MMAX RG CTX_AFREE pc.
Proof. intros pc H. exact H. Qed.
Lemma rr_post_xR_of_x : forall regs ly S Hp W mem md G0 FD es j h c O mx cap out kr W' c',
  rr_post_x B PST ARx MT RP RG regs ly S Hp W mem md G0 FD es j h c O mx cap out kr W' c' ->
  rr_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md G0 FD es j h c O mx cap out kr W' c'.
Proof.
intros regs ly S Hp W mem md G0 FD es j h c O mx cap out kr W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma rr_spec_xR_of_x : forall pc,
  rr_spec_x B PST ARx MT RP MMAX RG CTX_AFREE pc -> rr_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE pc.
Proof.
intros pc H. unfold rr_spec_xR. cbv zeta. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply rr_post_xR_of_x. exact HP.
Qed.
Lemma rig_post_x_wle : rig_post_x B PST ARx MT RP RG = rig_post_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma rig_spec_x_wle : rig_spec_x B PST ARx MT RP MMAX RG CTX_AFREE = rig_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG CTX_AFREE.
Proof. reflexivity. Qed.
Lemma rig_spec_x_of_xR : forall pc,
  rig_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG CTX_AFREE pc -> rig_spec_x B PST ARx MT RP MMAX RG CTX_AFREE pc.
Proof. intros pc H. exact H. Qed.
Lemma rig_post_xR_of_x : forall regs ly S Hp W mem md G0 ID es hs c O mx cap out kr W' c',
  rig_post_x B PST ARx MT RP RG regs ly S Hp W mem md G0 ID es hs c O mx cap out kr W' c' ->
  rig_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md G0 ID es hs c O mx cap out kr W' c'.
Proof.
intros regs ly S Hp W mem md G0 ID es hs c O mx cap out kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & qs & c2 & O2 & cap2 & out2 & rest & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k, qs, c2, O2, cap2, out2, rest. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma rig_spec_xR_of_x : forall pc,
  rig_spec_x B PST ARx MT RP MMAX RG CTX_AFREE pc -> rig_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE pc.
Proof.
intros pc H. unfold rig_spec_xR. cbv zeta. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply rig_post_xR_of_x. exact HP.
Qed.
End s6Ri.
