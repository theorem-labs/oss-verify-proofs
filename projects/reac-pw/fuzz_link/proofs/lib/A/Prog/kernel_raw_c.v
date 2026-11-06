(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v, with its module paths and module names changed; 517 of its 566 lines of code are new or changed and 594 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the raw path's chunk read:
   kr_c2 +0x1f4c -> kr_c3 +0x2074 (a chunk of t >= 1 bytes to copy) or kr_c7 +0x20f8 (no chunk).
   Listing (internal path) (internal record, sha256 7bc02d6772b3) +0x1f4c .. +0x20f8
   (fuzz_take): left = the cursor's bytes left. left = 0: +0x1fe0, take := 0. left >= 1: d0 := p[0], p += 1, left -= 1;
   left >= 2 (after the first): d1 := p[1], p += 1, left -= 1, nl := d0 + (d1 & 15) * 256 (+0x1fd4 .. +0x1fd8),
   take := min(nl + 1, left) (`bltu s11, a0` +0x2010); left = 1: take := 0. Then p += take, left -= take (+0x2024 ..
   +0x203c); the room test w1.n + take < 4097 (+0x2050: w1.n = 0, take <= 4096, never false); take = 0: `beqz a0` to
   +0x2078, w1.n += 0, the n_chunks test (j <= 2), `beqz s11` to +0x20f0, a0 := shadow(w1), a1 := 0x202 (kr_c7);
   take >= 1: a0 := w1 + w1.n, a1 := p', a2 := take (kr_c3).
   THE PROOF: the cut rebuilt as a symbolic state, per left = 0, 1, 2, >= 3 and per j = 0, 1, 2 (each state closed):
   the slots read-only, the cursor (atom 18) writable, the input bytes read (atom 33 = p, the bytes atoms 34, 35),
   w1.n (atom 36 = &w1.n) writable, n_chunks read-only; the shadow entries the cursor, the input bytes and w1.n
   (each range addressable: kernel_kit.v kn_cursor_ra, kernel_raw_kit.v kr_inp, kn_w1_ra). The engine decides every
   instrumented check; it stops at `bltu s11, a0` when take is symbolic (left >= 2) and at the room test (left >= 3):
   LinkPaLib.v psrr_branch_tok splits each, kernel_raw_kit.v kr_U_s11e gives nl + 1 = d0 + (d1 & 15) * 256 + 1 <= 4096
   and refutes the impossible sides. The cut after the run: kernel_raw_kit.v kr_land_cw (only the cursor and w1.n
   written) with the cursor restated from the end state's chunks (kr_kcursor_new).
   Section hypotheses: LAWS, LV, TB, KI, AMEMCPY, AMEMSET.
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit kernel_next kernel_qmsg_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_qmsg_a kernel_qmsg_b kernel_raw_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_raw_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


(* ---- the state at +0x1f4c: atoms 32 = left, 33 = p, 34 = d0, 35 = d1, 36 = &w1.n, 37 = shadow(w1) ---- *)
Definition rc_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x40 0xc8 0 0
    [YP09.mkChunk 0x40 (CVal 8 (SOff 36 (-4096))); YP09.mkChunk 0x48 (CVal 8 (SOff 36 0));
     YP09.mkChunk 0x50 (CVal 8 (SOff 37 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 243 0x40000));
     YP09.mkChunk 0xa8 (CVal 8 (SLit 4097)); YP09.mkChunk 0xc0 (CVal 8 (km_sh 18 0))].
Definition rc_cur (lv : sv) : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 lv)].
Definition rc_inch (k : Z) : list YP09.chunk :=
  if k =? 1 then [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]
  else [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0))].
Definition rc_in (k : Z) : YP09.region := YP09.mkRegion (Some 33%nat) 0 k 0 0 (rc_inch k).
Definition rc_wn (w : Z) : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 w [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition rc_g (j : Z) : YP09.region :=
  YP09.mkRegion (Some 243%nat) 0x40200 0x40204 0 0 [YP09.mkChunk 0x40200 (CVal 4 (SLit j))].
(* no input region when no input byte is read (left = 0) *)
Definition rc_rs (lv : sv) (k w j : Z) : list YP09.region :=
  if k =? 0 then [rc_sl; rc_cur lv; rc_wn w; rc_g j] else [rc_sl; rc_cur lv; rc_in k; rc_wn w; rc_g j].
Definition rc_atoms (la : afact) (k : Z) : list (nat * afact) :=
  [(18%nat, mkAF 0 (2 ^ 47 - 16) 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (243%nat, mkAF LA_G_NL LA_G_NL 0); (33%nat, mkAF 0 (2 ^ 47 - 1 - k) 0); (34%nat, mkAF 0 255 0);
   (35%nat, mkAF 0 255 0); (36%nat, mkAF 8192 (2 ^ 47 - 32) 5); (32%nat, la)].
Definition rc_ss (lv : sv) (la : afact) (k w j : Z) : sstate :=
  mkSS (kpc 0x1f4c) km_regsA (rc_rs lv k w j) None (mkFacts (rc_atoms la k) [] []).
Definition rc_SH (k : Z) : list shent :=
  if k =? 0 then [mkSHE 18 0 16; mkSHE 36 0 8] else [mkSHE 18 0 16; mkSHE 33 0 k; mkSHE 36 0 8].

(* ---- unsigned values of the engine's terms ---- *)
Lemma kr_U_rng : forall E a, 0 <= U E a < 2 ^ 64.
Proof.
  intros E a. unfold U. pose proof (bv_unsigned_in_range 64 (sv_denot E a)) as Hr.
  change (2 ^ 64) with (2 ^ Z.of_N 64). exact Hr.
Qed.

Lemma kr_ew_of_U : forall E n x, bv_unsigned (ew E n) = x -> ew E n = Z_to_bv 64 x.
Proof. intros E n x H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma kr_denot_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma kr_den_off : forall E n c x v, bv_unsigned (ew E n) = x -> x + c = v -> sv_denot E (SOff n c) = Z_to_bv 64 v.
Proof. intros E n c x v H Hv. cbn [sv_denot]. rewrite H, Hv. reflexivity. Qed.

Lemma kr_U_off : forall E n c x v, bv_unsigned (ew E n) = x -> x + c = v -> 0 <= v < 2 ^ 64 -> U E (SOff n c) = v.
Proof. intros E n c x v H Hv Hr. rewrite U_SOff, H, Hv. apply zcanon_id. unfold M64. lia. Qed.

Lemma kr_U_lit : forall E z v, z = v -> 0 <= v < 2 ^ 64 -> U E (SLit z) = v.
Proof. intros E z v Hv Hr. subst v. apply U_lit. exact Hr. Qed.

Lemma kr_U_add : forall E a b x y v, U E a = x -> U E b = y -> x + y = v -> v < 2 ^ 64 ->
  U E (SAlu ALU_ADD a b) = v.
Proof.
  intros E a b x y v Ha Hb Hv Hr. pose proof (kr_U_rng E a). pose proof (kr_U_rng E b).
  rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. rewrite Hv. apply zcanon_id. unfold M64. lia.
Qed.

Lemma kr_U_sub : forall E a b x y v, U E a = x -> U E b = y -> x - y = v -> 0 <= v ->
  U E (SAlu ALU_SUB a b) = v.
Proof.
  intros E a b x y v Ha Hb Hv Hr. pose proof (kr_U_rng E a). pose proof (kr_U_rng E b).
  rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. rewrite Hv. apply zcanon_id. unfold M64. lia.
Qed.

Lemma kr_U_s11eX : forall E d0 d1 v, bv_unsigned (ew E 34%nat) = d0 -> bv_unsigned (ew E 35%nat) = d1 ->
  0 <= d0 < 256 -> 0 <= d1 < 256 -> d0 + (d1 mod 16) * 256 + 1 = v ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 35 0) (SLit 60)) (SLit 52)))
         (SLit 1)) = v.
Proof.
  intros E d0 d1 v H34 H35 Hd0 Hd1 Hv. rewrite <- Hv.
  exact (proj1 (kr_U_s11e E d0 d1 (kr_ew_of_U E 34 d0 H34) (kr_ew_of_U E 35 d1 H35) Hd0 Hd1)).
Qed.

Lemma kr_U_sh : forall E c a v, bv_unsigned (ew E 18%nat) = a -> bv_unsigned (ew E 20%nat) = SHADOW_OFF ->
  0 <= a -> 0 <= c -> a + c < 2 ^ 47 -> SHADOW_OFF + (a + c) / 8 = v ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 c) (SLit 3)) (SOff 20 0)) = v.
Proof.
  intros E c a v H18 H20 Ha Hc Hac Hv.
  change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 c) (SLit 3)) (SOff 20 0)) with (km_sh 18 c).
  unfold U. rewrite (km_denot_sh E 18 a c (kr_ew_of_U E 18 a H18) Ha Hc ltac:(lia) (kr_ew_of_U E 20 SHADOW_OFF H20)).
  rewrite Hv. apply unsigned_lit_small. subst v.
  pose proof (Z.div_pos (a + c) 8 ltac:(lia) ltac:(lia)).
  assert ((a + c) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold SHADOW_OFF. lia.
Qed.

(* an atom's unsigned value from the context, the env possibly extended by a run's fresh atoms *)
Ltac rc_ea := first [eassumption | (cbn [ewset ew Nat.eqb]; eassumption)].

(* U of a term over the atoms whose unsigned values the context names *)
Ltac rcU :=
  first
  [ eapply kr_U_s11eX; [rc_ea | rc_ea | lia | lia | first [reflexivity | lia]]
  | eapply kr_U_sh; [rc_ea | rc_ea | lia | lia | lia | first [reflexivity | lia]]
  | eapply kr_U_add; [rcU | rcU | first [reflexivity | lia] | lia]
  | eapply kr_U_sub; [rcU | rcU | first [reflexivity | lia] | lia]
  | eapply kr_U_off; [rc_ea | first [reflexivity | lia] | lia]
  | eapply kr_U_lit; [first [reflexivity | lia] | lia] ].

(* env agreement with an env a run extended by fresh atoms *)
Lemma rc_agree_set : forall k E0 E' n v, (k <= n)%nat -> env_agree k E0 E' -> env_agree k E0 (ewset E' n v).
Proof.
  intros k E0 E' n v Hk H. eapply env_agree_trans; [exact H|]. eapply env_agree_le; [exact Hk|].
  apply env_agree_ewset.
Qed.
Ltac rc_agree HAG := first [exact HAG | apply rc_agree_set; [lia | rc_agree HAG]].

(* kernel_qmsg_b.v kq_un, the env possibly extended by a run's fresh atoms *)
Ltac rc_un HFr Zs :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
  intros a Ha Hna;
  apply (kept_of_frame (segs := pa_segs) _ _ _ _ _ Zs HFr); [ | exact Ha | exact Hna ];
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hxx := fresh "Hxx" in
  intros bb wl wh x Hin Hxx; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hxx; cbn [ewset ew Nat.eqb] in Hxx;
      repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hxx end;
      cbv beta; unfold NW_N, NW_FULL in *; clear - Hxx; lia
    | ]);
  destruct Hin.

(* a `bltu` condition as an inequality on values *)
Ltac rc_cond Hc :=
  rewrite branch_ltu_U in Hc;
  lazymatch type of Hc with (U ?E ?a <? U ?E ?b) = _ =>
    let Ha := fresh "Ua" in let Hb := fresh "Ub" in
    eassert (Ha : U E a = _); [rcU|]; eassert (Hb : U E b = _); [rcU|];
    rewrite Ha, Hb in Hc; clear Ha Hb
  end.

(* a register at the end of a run *)
Ltac rc_reg HS Ex ssx msn :=
  rewrite (st_ok_pi_restrict_reg _ Ex ssx msn _ HS);
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ =>
    let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end;
  apply kr_denot_of_U; rcU.

(* the writable bytes of a concrete region list: the cursor's and w1.n's *)
Ltac rc_wr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [ subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; cbn [ewset ew Nat.eqb] in Hr;
      repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hr end;
      first [left; lia | right; lia | exfalso; lia]
    | ]);
  destruct Hin.

(* every lemma of the Section below takes all its hypotheses (one calling convention for the lane) *)
Set Default Proof Using "All".

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.   (* checked_memset: AE2r.v asan_memset_realizes *)

(* the env at kr_c2 *)
Definition rc_E (ms : machine_state) (l p d0 d1 wn wsh : Z) : env :=
  Eimg (Ereg (ms_regs ms) [w64 l; w64 p; w64 d0; w64 d1; w64 wn; w64 wsh]).

Lemma rc_E_ext : forall ms l p d0 d1 wn wsh,
  ew (rc_E ms l p d0 d1 wn wsh) 32%nat = w64 l /\ ew (rc_E ms l p d0 d1 wn wsh) 33%nat = w64 p /\
  ew (rc_E ms l p d0 d1 wn wsh) 34%nat = w64 d0 /\ ew (rc_E ms l p d0 d1 wn wsh) 35%nat = w64 d1 /\
  ew (rc_E ms l p d0 d1 wn wsh) 36%nat = w64 wn /\ ew (rc_E ms l p d0 d1 wn wsh) 37%nat = w64 wsh.
Proof.
  intros. unfold rc_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
  refine (conj (ew_Ereg_extra _ _ 0) (conj (ew_Ereg_extra _ _ 1) (conj (ew_Ereg_extra _ _ 2)
    (conj (ew_Ereg_extra _ _ 3) (conj (ew_Ereg_extra _ _ 4) (ew_Ereg_extra _ _ 5)))))).
Qed.


(* the env's values at kr_c2 *)
Lemma rc_U : forall cx fpos k2 ly3 S3 md3 (ms3 : machine_state) ci adv d0 d1 (E : env),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kregs0 cx ms3 -> kregs_eq ms3 (kregs_chunk cx fpos ci) ->
  0 <= ci < 3 -> 0 <= adv <= k_wn cx -> 0 <= k_wp cx + adv < 2 ^ 47 -> k_wn cx < 2 ^ 64 ->
  0 <= d0 < 256 -> 0 <= d1 < 256 ->
  E = rc_E ms3 (k_wn cx - adv) (k_wp cx + adv) d0 d1 (kW1 cx fpos + NW_N) (kFSH cx fpos + 4) ->
  bv_unsigned (ew E 9%nat) = ksp1 cx /\ bv_unsigned (ew E 18%nat) = ka0 cx /\
  bv_unsigned (ew E 20%nat) = SHADOW_OFF /\ bv_unsigned (ew E 19%nat) = ka0 cx + 8 /\
  bv_unsigned (ew E 21%nat) = kW2 cx fpos /\ bv_unsigned (ew E 22%nat) = ci /\
  bv_unsigned (ew E 24%nat) = kS8 cx /\ bv_unsigned (ew E 25%nat) = kW2 cx fpos + NW_N /\
  bv_unsigned (ew E 32%nat) = k_wn cx - adv /\ bv_unsigned (ew E 33%nat) = k_wp cx + adv /\
  bv_unsigned (ew E 34%nat) = d0 /\ bv_unsigned (ew E 35%nat) = d1 /\
  bv_unsigned (ew E 36%nat) = kW1 cx fpos + NW_N /\ bv_unsigned (ew E 37%nat) = kFSH cx fpos + 4 /\
  bv_unsigned (ew E 243%nat) = LA_G_NL.
Proof.
  intros cx fpos k2 ly3 S3 md3 ms3 ci adv d0 d1 E HB HJB HR0 HRL Hci Hadv Hp Hwn Hd0 Hd1 HEdef.
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (rc_E_ext ms3 (k_wn cx - adv) (k_wp cx + adv) d0 d1 (kW1 cx fpos + NW_N) (kFSH cx fpos + 4))
    as (E32 & E33 & E34 & E35 & E36 & E37).
  rewrite <- HEdef in E32, E33, E34, E35, E36, E37.
  assert (ER : forall (q : nat) v, In (q, v) (kregs_chunk cx fpos ci) -> 0 <= v < 2 ^ 64 ->
            bv_unsigned (ew E q) = v).
  { intros q v Hin Hv. rewrite HEdef. unfold rc_E.
    apply (kr_U_reg ms3 (kregs_chunk cx fpos ci)); [exact HRL | exact Hin | | exact Hv].
    unfold kregs_chunk in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]). destruct Hin. }
  split; [rewrite HEdef; unfold rc_E; rewrite (ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl), A9; apply unsigned_lit_small; lia|].
  split; [rewrite HEdef; unfold rc_E; rewrite (ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl), A18; apply unsigned_lit_small; lia|].
  split; [rewrite HEdef; unfold rc_E; rewrite (ew_Eimg_Ereg_nat _ _ 20 20%bv eq_refl), A20; apply unsigned_lit_small;
          unfold SHADOW_OFF; lia|].
  split; [apply ER; [kr_in | lia]|].
  split; [apply ER; [kr_in | unfold kW2, KN_W2; lia]|].
  split; [apply ER; [kr_in | lia]|].
  split; [apply ER; [kr_in | unfold kS8, shadow_of_addr, SHADOW_OFF; lia]|].
  split; [apply ER; [kr_in | unfold kW2, KN_W2, NW_N; lia]|].
  split; [rewrite E32; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite E33; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite E34; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite E35; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite E36; unfold w64; apply unsigned_lit_small; unfold kW1, KN_W1, NW_N; lia|].
  split; [rewrite E37; unfold w64; apply unsigned_lit_small; unfold kHighMemBeg, SHADOW_OFF in *; lia|].
  rewrite HEdef. unfold rc_E. apply (kq_U243 SK B LAWS TB KI AMEMCPY LV).
Qed.

(* the input bytes a state reads *)
Lemma rc_bytes : forall cx fpos k2 ly3 S3 W3 ms3 md3 adv k,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  0 <= adv -> 0 <= k <= 2 -> adv + k <= k_wn cx ->
  exists d0 d1, 0 <= d0 < 256 /\ 0 <= d1 < 256 /\
    (1 <= k -> aview SEGS (w_H W3) (ms_mem ms3) (k_wp cx + adv) = Some d0) /\
    (2 <= k -> aview SEGS (w_H W3) (ms_mem ms3) (k_wp cx + adv + 1) = Some d1).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 adv k HB HJ HJB HKK Hadv Hk Hkl.
  destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
  - exists 0, 0. split; [lia|]. split; [lia|]. split; intros; lia.
  - destruct (kr_inp SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv) k HB HJ HJB HKK ltac:(lia) ltac:(lia) ltac:(lia))
      as (_ & _ & IPR & _).
    destruct (IPR (k_wp cx + adv) ltac:(lia)) as (v0 & Hv0).
    destruct (kr_inbyte SEGS _ _ _ v0 Hv0) as (_ & Hr0).
    destruct (Z.eq_dec k 1) as [Hk1 | Hk1].
    + exists v0, 0. split; [exact Hr0|]. split; [lia|]. split; [intros _; exact Hv0 | intros; lia].
    + destruct (IPR (k_wp cx + adv + 1) ltac:(lia)) as (v1 & Hv1).
      destruct (kr_inbyte SEGS _ _ _ v1 Hv1) as (_ & Hr1).
      exists v0, v1. split; [exact Hr0|]. split; [exact Hr1|]. split; intros _; assumption.
Qed.

(* the cursor's and w1.n's bytes are writable by kernel *)
Lemma rc_awr : forall cx fpos k2 ly3 S3 W3 mm md md0 (E : env) rs,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md k2 ->
  kjbk B cx fpos k2 ly3 S3 md0 -> m_fds md = m_fds md0 -> m_fs md = m_fs md0 ->
  (forall a, in_wrange E rs a -> (ka0 cx <= a < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= a < kW1 cx fpos + NW_N + 8)) ->
  awr_ok_x E rs (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md md0 E rs HB HJ HJB0 Hfds Hfs HW a Ha.
  assert (HJB : kjbk B cx fpos k2 ly3 S3 md) by exact (kjbk_md B cx fpos k2 ly3 S3 md0 md HJB0 Hfds Hfs).
  assert (HFA : frame_addr ly3 KN_CID fpos = kF cx fpos) by exact (km_fa SK B cx fpos k2 ly3 S3 W3 _ md HB HJ KN_CID fpos).
  destruct (HW a Ha) as [Hc | Hw].
  - apply (kq_ajw SK B cx fpos k2 ly3 S3 W3 _ md a HB HJ HJB).
    unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
    split; [unfold kernel_awr; km_inl | cbn [fst snd]; unfold ka0 in Hc; lia].
  - left.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos a HJ).
    + left. reflexivity.
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA, kn_fsb8. unfold kW1, KN_W1, NW_N in Hw. lia.
Qed.

(* ---- the state at kr_c2 ---- *)
Lemma rc_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv (lv : sv) la (k w : Z) d0 d1 (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW1 cx fpos) 0 0 ->
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  0 <= ci < 3 -> 0 <= j <= 2 -> (k = 0 \/ k = 1 \/ k = 2) -> k <= k_wn cx - adv -> (w = 0 \/ w = 8) ->
  (1 <= k -> aview SEGS (w_H W3) (ms_mem ms3) (k_wp cx + adv) = Some d0) ->
  (2 <= k -> aview SEGS (w_H W3) (ms_mem ms3) (k_wp cx + adv + 1) = Some d1) ->
  0 <= d0 < 256 -> 0 <= d1 < 256 ->
  E = rc_E ms3 (k_wn cx - adv) (k_wp cx + adv) d0 d1 (kW1 cx fpos + NW_N) (kFSH cx fpos + 4) ->
  sv_denot E lv = Z_to_bv 64 (k_wn cx - adv) -> afact_ok E 32 la ->
  regions_wf (rc_rs lv k w j) = true ->
  st_ok_pi SEGS pa_val E (rc_ss lv la k w j) (restrict (w_H W3) ms3) /\
  sh_ok SEGS kq_Bx (rc_SH k) E (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv lv la k w d0 d1 E HB HJ HW HK Hci Hj Hk Hkl Hw Hd0v Hd1v Hd0 Hd1
    HEdef Hlv Hla Hwf.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & HGN & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  destruct HCUR as (Hadv & HCP & HCN & HCW).
  destruct HW as (Ww0 & Wwl & Wpres & Wnv & Wfv & Wnr & Wfr).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  pose proof (kn_sp SK B cx HB) as (S1 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _ & F4 & _).
  rewrite kn_fsb8 in F2.
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp : k_wp cx + k_wn cx <= 2 ^ 47 - 1).
  { pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR. clear - HAMR. lia. }
  (* no disjunction stays in the context: lia would split on each *)
  assert (Hk' : 0 <= k <= 2) by (clear - Hk; lia).
  assert (Hw' : 0 <= w <= 8) by (clear - Hw; lia).
  clear Hk Hw.
  destruct (rc_U cx fpos k2 ly3 S3 md3 ms3 ci adv d0 d1 E HB HJB HR0 HRL Hci Hadv ltac:(lia) ltac:(lia) Hd0 Hd1 HEdef)
    as (U9 & U18 & U20 & U19 & U21 & U22 & U24 & U25 & U32 & U33 & U34 & U35 & U36 & U37 & U243).
  assert (E18 : ew E 18%nat = Z_to_bv 64 (ka0 cx)) by exact (kr_ew_of_U E 18 _ U18).
  assert (E20 : ew E 20%nat = Z_to_bv 64 SHADOW_OFF) by exact (kr_ew_of_U E 20 _ U20).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact U9.
  assert (BV18 : base_val E (Some 18%nat) = ka0 cx) by exact U18.
  assert (BV33 : base_val E (Some 33%nat) = k_wp cx + adv) by exact U33.
  assert (BV36 : base_val E (Some 36%nat) = kW1 cx fpos + NW_N) by exact U36.
  assert (BV243 : base_val E (Some 243%nat) = LA_G_NL) by exact U243.
  assert (SLx : forall o v, In (o, v) (kslots_setup cx fpos c) ->
            rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + o) = Some v)
    by (intros o v Hin; apply (kn_slot_of cx W3 ms3 _ o v HSL); unfold kr_sl; apply in_or_app; left; exact Hin).
  assert (SLR : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + KS_ROOM) = Some 4097)
    by (apply (kn_slot_of cx W3 ms3 _ KS_ROOM 4097 HSL); unfold kr_sl; apply in_or_app; right; left; reflexivity).
  (* the regions, each *)
  assert (RSL : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) rc_sl).
  { unfold rc_sl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x40 (SOff 36 (-4096)) (kW1 cx fpos));
        [apply (kr_den_off E 36 (-4096) _ _ U36); unfold NW_N; lia | apply SLx; unfold kslots_setup; kn_in].
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x48 (SOff 36 0) (kW1 cx fpos + NW_N));
        [apply (kr_den_off E 36 0 _ _ U36); lia | apply SLx; unfold kslots_setup; kn_in].
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x50 (SOff 37 0) (kFSH cx fpos + 4));
        [apply (kr_den_off E 37 0 _ _ U37); lia | apply SLx; unfold kslots_setup; kn_in].
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x70 (SOff 243 0x40000) (LA_G_NL + NK_CHUNK_LEN));
        [apply (kr_den_off E 243 0x40000 _ _ U243); unfold NK_CHUNK_LEN; lia | apply SLx; unfold kslots_setup; kn_in].
    - exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa8 (SLit 4097) 4097 eq_refl SLR).
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (km_sh 18 0) (shadow_of_addr SHADOW_OFF (ka0 cx)));
        [|apply SLx; unfold kslots_setup; kn_in].
      rewrite (km_denot_sh E 18 (ka0 cx) 0 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20), Z.add_0_r. reflexivity. }
  assert (RCUR : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (rc_cur lv)).
  { unfold rc_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCW o ltac:(lia))|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 33 0) (k_wp cx + adv));
        [apply (kr_den_off E 33 0 _ _ U33); lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
        | rewrite Z.add_0_r; exact HCP].
    - apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 lv (k_wn cx - adv));
        [exact Hlv | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact HCN]. }
  assert (RWN : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (rc_wn w)).
  { unfold rc_wn, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV36. split; [unfold kW1, KN_W1, NW_N; lia|]. split; [unfold kW1, KN_W1, NW_N; lia|]. split.
    { intros o Ho. replace (kW1 cx fpos + NW_N + o) with (kW1 cx fpos + (NW_N + o)) by lia.
      exact (proj2 (Wpres (NW_N + o) ltac:(unfold NW_N, NW_SIZE; lia))). }
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (kW1 cx fpos + NW_N) 0 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Wnv. }
  assert (RG : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (rc_g j)).
  { unfold rc_g, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV243. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ LA_G_NL 0x40200 4 (SLit j) j);
      [reflexivity | cbn; lia | cbn; lia | exact (kq_nchunks cx W3 ms3 j HGN)]. }
  assert (Gbase : forall rs, regions_wf rs = true -> Forall (region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3))) rs ->
            pairwise_disjoint E rs -> facts_ok E (mkFacts (rc_atoms la k) [] []) ->
            st_ok_pi SEGS pa_val E (mkSS (kpc 0x1f4c) km_regsA rs None (mkFacts (rc_atoms la k) [] []))
              (restrict (w_H W3) ms3)).
  { intros rs Hwf' HR Hpd HF.
    rewrite (km_ms_shape ms3 (BASE + kpc 0x1f4c) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
    pose proof (pa_entry_st_ok_full E (kpc 0x1f4c) sr_atoms (ms_regs ms3) rs (mkFacts (rc_atoms la k) [] [])
                  (mrestrict (w_H W3) (ms_mem ms3)) ltac:(rewrite HEdef; unfold rc_E; apply regs_ok_Eimg_Ereg)
                  Hwf' HR Hpd HF) as HS0.
    assert (HD19 : sv_denot E (SOff 18 8) = getr (ms_regs ms3) (Z_to_bv 5 19)).
    { rewrite (kr_den_off E 18 8 _ (ka0 cx + 8) U18 eq_refl). symmetry.
      exact (kn_reg_of ms3 _ 19 _ HRL ltac:(kr_in)). }
    assert (HD24 : sv_denot E (km_sh 18 8) = getr (ms_regs ms3) (Z_to_bv 5 24)).
    { rewrite (km_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
      symmetry. exact (kn_reg_of ms3 _ 24 _ HRL ltac:(kr_in)). }
    pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 19) (SOff 18 8) HS0 eq_refl HD19) as HS1.
    exact (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 24) (km_sh 18 8) HS1 eq_refl HD24). }
  assert (HF : facts_ok E (mkFacts (rc_atoms la k) [] [])).
  { unfold facts_ok, rc_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hla I))))))))); unfold afact_ok;
      cbn [af_lo af_hi af_al2].
    - rewrite U18. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    - rewrite U9. change (2 ^ 5) with 32. lia.
    - rewrite U20. change (2 ^ 0) with 1. rewrite Z.mod_1_r. unfold SHADOW_OFF. lia.
    - rewrite U243. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    - rewrite U33. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    - rewrite U34. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    - rewrite U35. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    - rewrite U36. change (2 ^ 5) with 32. unfold kW1, KN_W1, NW_N, alloc_ceiling in *. lia. }
  assert (HUB : U E kq_Bx = SHADOW_OFF)
    by (unfold kq_Bx; rewrite U_SOff, U20, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  pose proof (kn_cursor_ra SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HJB HKK) as HRAc.
  pose proof (kn_w1_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRAw.
  assert (SHc : shent_ok SEGS kq_Bx E (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE 18 0 16)).
  { apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 18 (ka0 cx) 16 (ka0 cx) 0 16 HRAc HUB);
      [rewrite U_SOff, U18, Z.add_0_r; apply zcanon_id; unfold M64; lia | lia | lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. destruct (CL x ltac:(lia)) as (CL1 & _).
    unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
  assert (SHw : shent_ok SEGS kq_Bx E (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE 36 0 8)).
  { apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 36 (kW1 cx fpos) NW_SIZE (kW1 cx fpos + NW_N) 0 8
             HRAw HUB);
      [rewrite U_SOff, U36, Z.add_0_r; apply zcanon_id; unfold M64, kW1, KN_W1, NW_N; lia
      | unfold NW_N; lia | unfold NW_N, NW_SIZE; lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (_ & _ & F3 & _).
    rewrite kn_fsb8 in F3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
    unfold kW1, KN_W1, NW_N, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  (* the separations the extents need, each proved in the disjunction-free context *)
  assert (Hslot : ksp cx - 4640 <= ksp1 cx + 0x40 /\ ksp1 cx + 0xc8 <= ksp cx) by lia.
  assert (DD : (ksp1 cx + 0xc8 <= ka0 cx \/ ka0 cx + 16 <= ksp1 cx + 0x40) /\
                (ka0 cx + 16 <= kW1 cx fpos + NW_N \/ kW1 cx fpos + NW_N + 8 <= ka0 cx) /\
                (ksp1 cx + 0xc8 <= kW1 cx fpos + NW_N \/ kW1 cx fpos + NW_N + 8 <= ksp1 cx + 0x40) /\
                (ksp1 cx + 0xc8 <= LA_G_NL + 0x40200 \/ LA_G_NL + 0x40204 <= ksp1 cx + 0x40) /\
                (ka0 cx + 16 <= LA_G_NL + 0x40200 \/ LA_G_NL + 0x40204 <= ka0 cx) /\
                (kW1 cx fpos + NW_N + 8 <= LA_G_NL + 0x40200 \/ LA_G_NL + 0x40204 <= kW1 cx fpos + NW_N)).
  { split.
    { pose proof (proj2 (CL (ka0 cx) ltac:(lia))) as C0. pose proof (proj2 (CL (ka0 cx + 15) ltac:(lia))) as C15.
      rewrite HK8 in C0, C15. clear - Hslot C0 C15. lia. }
    split.
    { pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx) HB HJB (kn_ard_cur cx (ka0 cx) ltac:(lia))) as N0.
      pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx + 15) HB HJB
                    (kn_ard_cur cx (ka0 cx + 15) ltac:(lia))) as N15.
      rewrite kn_fsb8 in N0, N15. unfold kW1, KN_W1, NW_N. clear - N0 N15. lia. }
    split; [unfold kW1, KN_W1, NW_N, alloc_ceiling in *; lia|].
    split; [unfold LA_G_NL; lia|].
    split.
    { pose proof (kn_apre SK B cx HB) as (AG & _). unfold apart_gnl, NK_SIZE in AG. clear - AG. lia. }
    { destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (_ & _ & _ & _ & F5 & _).
      rewrite kn_fsb8 in F5. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
      unfold kW1, KN_W1, NW_N, LA_G_NL. clear - F5. lia. } }
  destruct DD as (Dsc & Dcw & Dsw & Dsg & Dcg & Dwg).
  destruct (Z.eq_dec k 0) as [Hk0 | Hk12].
  - (* no input byte read *)
    subst k. unfold rc_ss, rc_rs, rc_SH in *. cbn [Z.eqb] in *. split.
    + apply Gbase; [exact Hwf | repeat apply Forall_cons; try apply Forall_nil; assumption | | exact HF].
      apply pairwise_disjoint_of_extents. unfold extent_of_region, rc_sl, rc_cur, rc_wn, rc_g.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV18, BV36, BV243.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      (repeat split; first [ clear - Dsc; lia | clear - Dcw; lia | clear - Dsw; lia | clear - Dsg; lia
                           | clear - Dcg; lia | clear - Dwg; lia ]).
    + unfold sh_ok. repeat apply Forall_cons; try apply Forall_nil; assumption.
  - (* one or two input bytes read *)
    assert (Hk0 : (k =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (Hk1 : 1 <= k) by (clear - Hk' Hk12; lia). clear Hk12.
    unfold rc_ss, rc_rs, rc_SH in *. rewrite Hk0 in *.
    destruct (kr_inp SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv) k HB HJ HJB HKK
                ltac:(lia) ltac:(lia) ltac:(lia)) as (IRA & _ & _ & _ & IWN & ILO).
    assert (DI : (ksp1 cx + 0xc8 <= k_wp cx + adv \/ k_wp cx + adv + k <= ksp1 cx + 0x40) /\
                 (ka0 cx + 16 <= k_wp cx + adv \/ k_wp cx + adv + k <= ka0 cx) /\
                 (kW1 cx fpos + NW_N + 8 <= k_wp cx + adv \/ k_wp cx + adv + k <= kW1 cx fpos + NW_N) /\
                 (LA_G_NL + 0x40204 <= k_wp cx + adv \/ k_wp cx + adv + k <= LA_G_NL + 0x40200)).
    { assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
      split.
      { pose proof (IWN (k_wp cx + adv) ltac:(lia)) as L7. pose proof (IWN (k_wp cx + adv + k - 1) ltac:(lia)) as L8.
        rewrite HK8 in L7, L8. clear - Hslot L7 L8 Hk' Hk1. unfold ksp in *. lia. }
      split.
      { pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & _ & (_ & _ & _ & HAPc)). unfold apart in HAPc.
        clear - HAPc Hk' Hk1 Hkl Hadv. unfold ka0 in *. lia. }
      split.
      { destruct (ILO (k_wp cx + adv) ltac:(lia)) as (_ & _ & L3).
        destruct (ILO (k_wp cx + adv + k - 1) ltac:(lia)) as (_ & _ & L6). rewrite Hfb in L3, L6.
        clear - L3 L6 Hk' Hk1. unfold kW1, KN_W1, NW_N. lia. }
      { pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & _ & (_ & HAPg & _ & _)). unfold apart_gnl in HAPg.
        clear - HAPg Hk' Hk1 Hkl Hadv. unfold NK_SIZE in *. lia. } }
    destruct DI as (Dis & Dic & Diw & Dig).
    assert (RIN : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (rc_in k)).
    { unfold rc_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite BV33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      destruct (kr_inbyte SEGS (w_H W3) (ms_mem ms3) _ d0 (Hd0v ltac:(lia))) as (Hv0 & _).
      assert (Hk12' : k = 1 \/ k = 2) by (clear - Hk' Hk1; lia).
      clear Dsc Dcw Dsw Dsg Dcg Dwg Dis Dic Diw Dig.
      destruct Hk12' as [-> | ->]; unfold rc_inch; cbn [Z.eqb Pos.eqb]; repeat apply Forall_cons; try apply Forall_nil.
      - apply (chunk_ok_val SEGS E _ (k_wp cx + adv) 0 1 (SOff 34 0) d0);
          [apply (kr_den_off E 34 0 _ _ U34); lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hv0].
      - apply (chunk_ok_val SEGS E _ (k_wp cx + adv) 0 1 (SOff 34 0) d0);
          [apply (kr_den_off E 34 0 _ _ U34); lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hv0].
      - destruct (kr_inbyte SEGS (w_H W3) (ms_mem ms3) _ d1 (Hd1v ltac:(lia))) as (Hv1 & _).
        apply (chunk_ok_val SEGS E _ (k_wp cx + adv) 1 1 (SOff 35 0) d1);
          [apply (kr_den_off E 35 0 _ _ U35); lia | cbn; lia | cbn; lia | exact Hv1]. }
    split.
    + apply Gbase; [exact Hwf | repeat apply Forall_cons; try apply Forall_nil; assumption | | exact HF].
      apply pairwise_disjoint_of_extents. unfold extent_of_region, rc_sl, rc_cur, rc_in, rc_wn, rc_g.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV18, BV33, BV36, BV243.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      (repeat split; first [ clear - Dsc; lia | clear - Dcw; lia | clear - Dsw; lia | clear - Dsg; lia
                           | clear - Dcg; lia | clear - Dwg; lia | clear - Dis; lia | clear - Dic; lia
                           | clear - Diw; lia | clear - Dig; lia ]).
    + unfold sh_ok. apply Forall_cons; [exact SHc|]. apply Forall_cons; [|apply Forall_cons; [exact SHw | apply Forall_nil]].
      clear Dsc Dcw Dsw Dsg Dcg Dwg Dis Dic Diw Dig.
      apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 33 (k_wp cx + adv) k (k_wp cx + adv) 0 k IRA HUB);
        [rewrite U_SOff, U33, Z.add_0_r; apply zcanon_id; unfold M64; lia | lia | lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
      destruct (ILO x ltac:(lia)) as (_ & I2 & _). unfold SHADOW_OFF in *. lia.
Qed.

(* ---- the cut after a run that took no chunk: kr_c7 ---- *)
Lemma rc_land7 : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv a (ms : machine_state) md,
  kfrom SK B POST (kr_c7 B Rc) ->
  kbase SK B cx -> frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  0 <= adv + a <= k_wn cx ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (ka0 cx + 0) 8 (k_wp cx + (adv + a)) ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (ka0 cx + 8) 8 (k_wn cx - (adv + a)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ ((ka0 cx <= x < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= x < kW1 cx fpos + NW_N + 8)) ->
     aview SEGS (w_H W3) (ms_mem ms) x = aview SEGS (w_H W3) (ms_mem ms3) x) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  kms 0x20f8 ms -> kregs0 cx ms -> kregs_eq ms (kr_rl7 cx fpos ci) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv a ms md HN HB HFRM HJ HRc Hc Hci Hj HK Ha V0 V8 UN HG
    HMS HR0 HRL Hfds Hfs.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HCUR & _).
  rewrite Z.add_0_r in V0.
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFRM).
  exists c, ci, j, (adv + a). split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [lia|].
  apply (kr_land_cw SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c)
           (kfsh 0 0xf8 0xf3) adv (Some j) k2 ly3 S3 W3 ms3 md3 ms md 0x20f8 (kr_rl7 cx fpos ci) (adv + a) HB HK
           (kfsh_fits _ _ _) (kr_sl_ok cx fpos c) UN (fun x Hx => kq_apres_grows _ _ _ x HG Hx) Hfds Hfs HMS HR0 HRL).
  exact (kr_kcursor_new SK B LAWS LV TB KI AMEMCPY AMEMSET cx W3 ms3 ms adv (adv + a) HCUR Ha V0 V8
           (fun x Hx => kq_apres_grows _ _ _ x HG Hx)).
Qed.

(* ---- the cut after a run that took a chunk of t bytes: kr_c3 ---- *)
Lemma rc_land3 : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv t (ms : machine_state) md,
  kfrom SK B POST (kr_c3 B Rc) ->
  kbase SK B cx -> frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW1 cx fpos) 0 0 ->
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  1 <= t <= 4096 -> 0 <= adv -> adv + 2 + t <= k_wn cx ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (ka0 cx + 0) 8 (k_wp cx + (adv + 2 + t)) ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (ka0 cx + 8) 8 (k_wn cx - (adv + 2 + t)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (ka0 cx <= x < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms) x = aview SEGS (w_H W3) (ms_mem ms3) x) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  kms 0x2074 ms -> kregs0 cx ms -> kregs_eq ms (kr_rl3 cx fpos ci t (k_wp cx + (adv + 2 + t) - t)) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv t ms md HN HB HFRM HJ HRc Hc Hci Hj HW HK Ht Hadv Hl V0 V8 UN
    HG HMS HR0 HRL Hfds Hfs.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _ & HCUR & _).
  rewrite Z.add_0_r in V0.
  assert (HP : forall x, apresent (w_H W3) (ms_mem ms3) x -> apresent (w_H W3) (ms_mem ms) x)
    by exact (fun x Hx => kq_apres_grows _ _ _ x HG Hx).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFRM).
  exists c, ci, j, (adv + 2 + t), t. split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [lia|].
  split; [exact Ht|]. split; [lia|].
  split; [exact (kr_kw_cur SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 md3 W3 ms3 ms 0 0 HB HJB HW UN HP)|].
  apply (kr_land_cw SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c)
           (kfsh 0 0xf8 0xf3) adv (Some j) k2 ly3 S3 W3 ms3 md3 ms md 0x2074 _ (adv + 2 + t) HB HK
           (kfsh_fits _ _ _) (kr_sl_ok cx fpos c)); [| exact HP | exact Hfds | exact Hfs | exact HMS | exact HR0
           | exact HRL |].
  - intros x Hx Hn. apply UN; [exact Hx|]. intros Hc'. apply Hn. left. exact Hc'.
  - exact (kr_kcursor_new SK B LAWS LV TB KI AMEMCPY AMEMSET cx W3 ms3 ms adv (adv + 2 + t) HCUR ltac:(lia) V0 V8 HP).
Qed.

End b.
End a.
