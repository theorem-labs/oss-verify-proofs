(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module names changed; 922 of its 964 lines of code are new or changed and 297 lines of the source are left out. *)
(* text_of (fuzz_link.asan 0x87dc0) on image A: the U16 segment of its walk, from the U16 cut
   (lib/A/Prog/text_ofKit.v, +0x1a8) to the MALLOC cut (wrapper_malloc's entry)
   (listing (internal path) (internal record, sha256 1c4fdcbb52aa)):
     +0x1a8..+0x1dc  v := b2 * 256 + b1; want := v mod 320 (multiply by 0xcccd, shift 24, times 320, subtract)
     +0x1d0          ld rem := count;  +0x1e0..+0x1e4  n := min (want, rem) (bltu)
     +0x1e8..+0x208  q := cursor; cursor := q + n; count := rem - n
     +0x20c          n = 0 -> +0x298 (k := 0)
     +0x210..+0x21c  wrapper_memchr (q, 0, n);  +0x220..+0x224  k := the index of the first NUL, or n
     +0x228..+0x22c  wrapper_malloc (k + 1): the MALLOC cut
   The cut's state is rebuilt from to_gi_u16 (registers as atoms, a0 / a4 / a5 / s5 set to the address forms the
   token runner checks), want = v mod 320 is proved over the 65536 byte pairs (tu_want_val), and the four arms
   (n = want or rem; n = 0 or memchr) end at the MALLOC cut through tu_gi_mal_of, which carries the U16 cut's core
   across the stretch (tu_core_step: only the cursor and memchr's window below the frame change). memchr's
   constants are apart from the cursor and *own by apre's last conjunct (write-set bytes are not in_roP).

   Section hypotheses: LAWS, MEMCHR (lib/A/Rt/RtClosed.v link_memchrM_closed), MC_RO (LinkWalkMemchr.v
   link_mc_ro).

   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b YC88.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkCall LinkWalkNoWrite LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_writeArmsA model_writeSendA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import MemchrDef ConstsViewDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMemchr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs text_ofKit text_ofHead.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut's state: s4 (atom 20) the shadow base; the cursor (atom 12 = a2 = p) with its words q (atom 32) and
   rem (atom 33); b1 (atom 16 = a6) and b2 (atom 11 = a1) *)
Definition TUBx : sv := SOff 20 0.
Definition tu_fA : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (12%nat, mkAF 0 (2 ^ 47 - 17) 3); (16%nat, mkAF 0 255 0); (11%nat, mkAF 0 255 0);
   (32%nat, mkAF 0 (2 ^ 47) 0); (33%nat, mkAF 0 (2 ^ 47) 0)].
Definition tu_rP : YP09.region := YP09.mkRegion (Some 12%nat) 0 16 0 16
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition tu_ss : sstate := mkSS TO_CUT_U16 sr_atoms [tu_rP] None (mkFacts tu_fA [] []).
Definition tu_SH : list shent := [mkSHE 12 0 16].

(* the shadow address of an atom plus a constant, the shadow base in atom bn (srli 3, add) *)
Lemma tu_shadow_sv : forall Ev n k v bn, bv_unsigned (ew Ev n) = v -> 0 <= v + k < 2 ^ 64 ->
  bv_unsigned (ew Ev bn) = SHADOW_OFF ->
  sv_denot Ev (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff bn 0)) = Z_to_bv 64 (SHADOW_OFF + (v + k) / 8).
Proof.
  intros Ev n k v bn H Hk Hb.
  rewrite (denot_lit_U Ev (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff bn 0))).
  rewrite U_SAlu, U_SAlu, !U_SOff, U_SLit. cbn [zalu_raw]. rewrite H, Hb. unfold zcanon, M64.
  f_equal. rewrite (Z.mod_small (v + k)) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite Z.add_0_r, (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite (Z.mod_small ((v + k) / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hd : 0 <= (v + k) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small; [lia|]. unfold SHADOW_OFF. lia.
Qed.

(* v = b2 * 256 + b1 (+0x1b0 slli, +0x1b8 or) and want = v mod 320 (+0x1bc .. +0x1dc), as the runner forms them *)
Definition tu_v : sv := SAlu ALU_OR (SAlu ALU_SLL (SOff 11 0) (SLit 8)) (SOff 16 0).
Definition tu_want : sv :=
  SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_SUB tu_v
    (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL tu_v (SLit 52429)) (SLit 24)) (SLit 320))) (SLit 48)) (SLit 48).

Definition tu_z256 : list Z := map Z.of_nat (seq 0 256).
Lemma tu_z256_in : forall b, 0 <= b < 256 -> In b tu_z256.
Proof.
  intros b Hb. unfold tu_z256. apply in_map_iff. exists (Z.to_nat b). split; [apply Z2Nat.id; lia|].
  apply in_seq. lia.
Qed.
(* a property of two bytes, by computation over the 65536 pairs *)
Lemma tu_exhaust : forall F : Z -> Z -> bool,
  forallb (fun b2 => forallb (fun b1 => F b1 b2) tu_z256) tu_z256 = true ->
  forall b1 b2, 0 <= b1 < 256 -> 0 <= b2 < 256 -> F b1 b2 = true.
Proof.
  intros F H b1 b2 H1 H2. rewrite forallb_forall in H. specialize (H b2 (tu_z256_in b2 H2)).
  rewrite forallb_forall in H. exact (H b1 (tu_z256_in b1 H1)).
Qed.

Lemma tu_want_val : forall Ev b1 b2, bv_unsigned (ew Ev 16) = b1 -> bv_unsigned (ew Ev 11) = b2 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 -> U Ev tu_want = (b1 + 256 * b2) mod 320 /\ U Ev tu_v = b1 + 256 * b2.
Proof.
  intros Ev b1 b2 H1 H2 R1 R2. unfold tu_want, tu_v.
  repeat first [rewrite U_SAlu | rewrite U_SMd | rewrite U_SOff | rewrite U_SLit]. rewrite H1, H2.
  cbn [zalu_raw zmd_raw].
  clear H1 H2. revert b1 b2 R1 R2.
  intros b1 b2 R1 R2; split; apply Z.eqb_eq;
  match goal with |- (?L =? ?R) = true =>
    let f := eval pattern b1, b2 in (L =? R) in
    lazymatch f with ?F ?x ?y => change (F x y = true); apply (tu_exhaust F); [vm_compute; reflexivity | exact R1 | exact R2] end
  end.
Qed.

(* the shadow byte of an application byte *)
Lemma tu_shadow_rng : forall p n x, 0 <= p ->
  (p + n <= 0x7fff8000 - 1 \/ (0x10007fff8000 <= p /\ p + n <= 0x800000000000 - 1)) -> p <= x < p + n ->
  0x7fff8000 <= shadow_of_addr SHADOW_OFF x < 0x7fff8000 + 2 ^ 44.
Proof.
  intros p n x H0 H Hx. unfold shadow_of_addr, SHADOW_OFF.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.

(* a register of an st_ok state as the denotation of its symbolic value *)
Ltac to_reg_raw_st HS r Q :=
  lazymatch type of HS with st_ok ?segs ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H Ev ss ms r HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q end.

(* a symbolic value over atoms 32 / 33 as a number *)
Ltac tu_uval V32 V33 :=
  try change (bv_unsigned (sv_denot ?Ev ?e)) with (U Ev e);
  repeat first [rewrite U_SAlu | rewrite U_SOff | rewrite U_SLit]; cbn [zalu_raw]; rewrite ?V32, ?V33;
  unfold zcanon, M64; rewrite ?Z.add_0_r.

(* a register's symbolic value as a number, over want (UW), memchr's result (UA) and atoms 32 / 33 *)
Ltac tu_regv Ev UW UA VA VB :=
  rewrite (denot_lit_U Ev); unfold w64; f_equal; fold tu_v; fold tu_want;
  repeat first [rewrite UW | rewrite UA | rewrite U_SAlu | rewrite U_SMd | rewrite U_SOff | rewrite U_SLit];
  cbn [zalu_raw zmd_raw]; rewrite ?VA, ?VB; unfold zcanon, M64; rewrite ?Z.add_0_r.
(* a chunk's word value, read off V, as the number target *)
Ltac tu_chunk V UW UA VA VB target fin :=
  lazymatch type of V with context [bv_unsigned (sv_denot ?Ev ?e)] =>
    let Hv := fresh "Hv" in
    assert (Hv : bv_unsigned (sv_denot Ev e) = target);
    [ change (bv_unsigned (sv_denot Ev e)) with (U Ev e); fold tu_v; fold tu_want;
      repeat first [rewrite UW | rewrite UA | rewrite U_SAlu | rewrite U_SMd | rewrite U_SOff | rewrite U_SLit];
      cbn [zalu_raw zmd_raw]; rewrite ?VA, ?VB; unfold zcanon, M64; rewrite ?Z.add_0_r; fin
    | rewrite Hv in V; exact V ] end.

(* a run's write permission: the cursor (atom 12), a write-set byte *)
Ltac tu_awr Hajw Up :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite ?Up in Hx;
      first [ lia | apply Hajw; eexists; split; [left; reflexivity | cbn [fst snd]; lia] ]
    |]);
  apply awr_ok_x_nil.

Lemma tu_in_firstn : forall (l : list byte) k x, In x (firstn k l) -> exists i, (i < k)%nat /\ nth_error l i = Some x.
Proof.
  induction l as [|y l IH]; intros k x H; destruct k as [|k]; cbn in H; try contradiction.
  destruct H as [<- | H]; [exists 0%nat; split; [lia | reflexivity]|].
  destruct (IH k x H) as (i & Hi & Hn). exists (S i). split; [lia | exact Hn].
Qed.
Lemma tu_nth_skipn : forall (l : list byte) a i, nth_error (skipn a l) i = nth_error l (a + i).
Proof. induction l as [|y l IH]; intros [|a] i; cbn; try reflexivity. destruct i; reflexivity. apply IH. Qed.
Lemma tu_grows_of_present : forall H m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Eh; [exact Hx|].
  destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Ha : apresent H m (bv_unsigned x)).
  { unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
  destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
(* wrapper_memchr (0x43060): lib/A/Rt/RtClosed.v link_memchrM_closed; its 32 constant bytes: LinkWalkMemchr.v
   link_mc_ro *)
Hypothesis MEMCHR : amemchr_realizesM SEGS B 0x10360 0x10380 (pa_sigma LS___interceptor_trampoline_memchr).
Hypothesis MC_RO : forall a, 0x10360 <= a < 0x10380 -> in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4).

Lemma tu_ms_eta : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

(* a word read where the reader is unchanged *)
Lemma tu_rdword_eq : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) ->
  rdword r' a = rdword r a.
Proof.
  intros r r' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  unfold rdword. rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* a cut before the malloc carried across a stretch that writes only X: the cursor and the callees' window below
   the frame *)
Lemma tu_core_step : forall cx (ms3 msF : machine_state) md3 mdF pcv (X : Z -> Prop) v0 v1,
  to_pre SK B MT CTX cx -> to_core SK B cx ms3 md3 ->
  msF = mkst (ms_regs msF) pcv (ms_mem msF) (seg_rom SEGS) ->
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (ms_mem msF) mdF (to_k cx) ->
  m_fds mdF = m_fds (to_mdc cx) -> m_fs mdF = m_fs (to_mdc cx) ->
  getr (ms_regs msF) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs msF) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs msF) 20 = getr (ms_regs ms3) 20 ->
  (forall r, In r TO_UNTOUCHED -> getr (ms_regs msF) (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)) ->
  (forall a, X a -> to_sp cx - TEXT_OF_AK <= a < to_sp cx - TO_FRAME \/ to_p cx <= a < to_p cx + 16) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
     aview SEGS (w_H (to_W cx)) (ms_mem msF) a = aview SEGS (w_H (to_W cx)) (ms_mem ms3) a) ->
  mem_grows (rdW (to_W cx) (ms_mem ms3)) (rdW (to_W cx) (ms_mem msF)) ->
  au64_at SEGS (rdW (to_W cx) (ms_mem msF)) (to_p cx) v0 ->
  au64_at SEGS (rdW (to_W cx) (ms_mem msF)) (to_p cx + 8) v1 ->
  to_core SK B cx msF mdF.
Proof.
  intros cx ms3 msF md3 mdF pcv X v0 v1 HPX HC Hms HJ Hfd Hfs R2 R8 R20 RU HX KEEP GR V0 V1.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & R2c & R8c & R20c & RUc & SVc & UNc & PRc & WPc & BPc & VOc & BOc).
  destruct (ms_shape_mkst SEGS msF _ _ _ Hms) as (Hrv & Hsv & Hrom & Hfr & Hfc & _).
  pose proof (to_win SK B MT CTX cx HPX) as (Hceil & H47 & _ & Hw1 & Hw2).
  pose proof (to_pre_P SK B MT CTX cx HPX) as
    (c0 & c1 & inp & _ & _ & _ & _ & _ & _ & _ & _ & Hafp & _ & _ & _ & _ & Hafo & Hapo & _).
  pose proof asan_consts as ((C1a & C1b) & _ & _ & _ & _).
  assert (HK : TEXT_OF_AK = 16448) by reflexivity.
  assert (Hp0 : 0 <= to_p cx < 2 ^ 64) by (unfold to_p, aarg, argZ; apply bv_unsigned_in_range).
  assert (Ho0 : 0 <= to_o cx < 2 ^ 64) by (unfold to_o, aarg, argZ; apply bv_unsigned_in_range).
  unfold apart_frame, apart in Hafp, Hafo, Hapo. change (aarg (to_regs cx) 0) with (to_p cx) in Hafp, Hapo.
  change (aarg (to_regs cx) 1) with (to_o cx) in Hafo, Hapo. change (spZ (to_regs cx)) with (to_sp cx) in Hafp, Hafo.
  unfold TO_FRAME in HX.
  unfold to_core. cbv zeta.
  do 8 (split; [assumption|]).
  split; [rewrite R2; exact R2c|]. split; [rewrite R8; exact R8c|]. split; [rewrite R20; exact R20c|].
  split; [intros r Hr; rewrite (RU r Hr); exact (RUc r Hr)|].
  split.
  { intros j Hj. rewrite <- (SVc j Hj). apply tu_rdword_eq. intros i Hi. apply KEEP; [lia|].
    intros HXa. destruct (HX _ HXa) as [Ha | Ha]; lia. }
  split.
  { intros a Ha Hw HE. rewrite KEEP; [exact (UNc a Ha Hw HE) | exact Ha |].
    intros HXa. destruct (HX _ HXa) as [Hb | Hb]; [apply Hw; lia|].
    apply HE. unfold to_E, inFP, to_wr, text_of_awr. exists (to_p cx, to_p cx + 16).
    split; [left; reflexivity | cbn [fst snd]; exact Hb]. }
  split; [intros a Ha; exact (to_grow _ _ _ GR a (PRc a Ha))|].
  split.
  { intros a Ha. apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
  destruct BPc as (jp & Hjp & (Hp0' & Hp1 & _) & Hwp). rewrite Hjp in Hp1, Hwp.
  destruct BOc as (jo & Hjo & (Ho0' & Ho1 & _) & Hwo). rewrite Hjo in Ho1, Hwo.
  split; [apply (to_abuf16 _ _ v0 v1 Hp0' Hp1 V0 V1); exact (to_awrange_grows _ _ _ _ Hwp GR)|].
  assert (VO : au64_at SEGS (rdW (to_W cx) (ms_mem msF)) (to_o cx) 0).
  { intros kk Hk. rewrite <- (VOc kk Hk). apply (mbyte_of_aview_eq SEGS). apply KEEP; [lia|].
    intros HXa. destruct (HX _ HXa) as [Ha | Ha]; lia. }
  split; [exact VO|].
  apply (to_abuf8 _ _ 0 Ho0' Ho1 VO). exact (to_awrange_grows _ _ _ _ Hwo GR).
Qed.

Lemma tu_sbm_fds : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' H. unfold same_but_materialized in H. rewrite H. apply wvb_fds_fs. Qed.

(* the first k bytes from adv on hold no NUL, from memchr's first_byte over a view of the input *)
Lemma tu_nul_free : forall (m : word -> option byte) c0 inp adv k,
  abytes SEGS m c0 inp -> 0 <= adv -> 0 <= k -> adv + k <= Z.of_nat (length inp) ->
  (forall i, 0 <= i < k -> exists b, ard SEGS m (c0 + adv + i) = Some b /\ b <> 0) ->
  ~ In (zb 0) (firstn (Z.to_nat k) (skipn (Z.to_nat adv) inp)).
Proof.
  intros m c0 inp adv k (_ & _ & Hab) Ha Hk Hl Hnz Hin.
  destruct (tu_in_firstn _ _ _ Hin) as (i & Hi & Hn). rewrite tu_nth_skipn in Hn.
  destruct (Hnz (Z.of_nat i) ltac:(lia)) as (b & Hb & Hb0). unfold ard in Hb.
  replace (c0 + adv + Z.of_nat i) with (c0 + Z.of_nat (Z.to_nat adv + i)) in Hb by lia.
  rewrite (Hab (Z.to_nat adv + i)%nat ltac:(lia)), Hn in Hb. cbn in Hb. injection Hb as <-.
  apply Hb0. reflexivity.
Qed.

(* the MALLOC cut from a run's last state: the U16 cut's core carried across, the input consumed and the call's
   registers *)
Lemma tu_gi_mal_of : forall cx (ms3 msF : machine_state) md3 mdF c0 c1 inp adv n k pcv (X : Z -> Prop),
  to_pre SK B MT CTX cx -> to_core SK B cx ms3 md3 -> to_inp cx c0 c1 inp ->
  msF = mkst (ms_regs msF) pcv (ms_mem msF) (seg_rom SEGS) ->
  ms_pc_val msF = w64 (pa_sigma LS___interceptor_trampoline_malloc) ->
  getr (ms_regs msF) 1 = w64 (BASE + TO_MAL_RA) ->
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (ms_mem msF) mdF (to_k cx) ->
  m_fds mdF = m_fds (to_mdc cx) -> m_fs mdF = m_fs (to_mdc cx) ->
  getr (ms_regs msF) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs msF) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs msF) 20 = getr (ms_regs ms3) 20 ->
  (forall r, In r TO_UNTOUCHED -> getr (ms_regs msF) (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)) ->
  (forall a, X a -> to_sp cx - TEXT_OF_AK <= a < to_sp cx - TO_FRAME \/ to_p cx <= a < to_p cx + 16) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
     aview SEGS (w_H (to_W cx)) (ms_mem msF) a = aview SEGS (w_H (to_W cx)) (ms_mem ms3) a) ->
  mem_grows (rdW (to_W cx) (ms_mem ms3)) (rdW (to_W cx) (ms_mem msF)) ->
  1 <= adv <= 3 -> adv + n <= c1 -> 0 <= k <= n -> n <= 319 ->
  ~ In (zb 0) (firstn (Z.to_nat k) (skipn (Z.to_nat adv) inp)) ->
  getr (ms_regs msF) 10 = w64 (k + 1) -> getr (ms_regs msF) 9 = w64 k -> getr (ms_regs msF) 18 = w64 (c0 + adv) ->
  getr (ms_regs msF) 21 = w64 (SHADOW_OFF + to_o cx / 8) ->
  au64_at SEGS (rdW (to_W cx) (ms_mem msF)) (to_p cx) (c0 + adv + n) ->
  au64_at SEGS (rdW (to_W cx) (ms_mem msF)) (to_p cx + 8) (c1 - adv - n) ->
  to_gi_mal SK B cx msF mdF.
Proof.
  intros cx ms3 msF md3 mdF c0 c1 inp adv n k pcv X HPX HC HI Hms Hpc R1 HJ Hfd Hfs R2 R8 R20 RU HX KEEP GR
    Ha Hn Hk Hn3 Hnz R10 R9 R18 R21 P0 P8.
  unfold to_gi_mal. cbv zeta. exists c0, c1, inp, adv, n, k.
  split; [exact Hpc|]. split; [exact R1|].
  split; [exact (tu_core_step cx ms3 msF md3 mdF pcv X _ _ HPX HC Hms HJ Hfd Hfs R2 R8 R20 RU HX KEEP GR P0 P8)|].
  repeat (split; [assumption|]). exact P8.
Qed.

(* fold a run's frame and growth onto the bytes kept since the cut (outside Zs) *)
Ltac tu_fold UN GR Zs Up :=
  lazymatch type of UN with forall a, _ -> _ -> aview ?sg (w_H ?Wx) ?mOld a = aview _ _ ?m0 a =>
  lazymatch goal with
  | HFrx : frame_of ?Ex ?rsx (mrestrict (w_H Wx) mOld) (mrestrict (w_H Wx) ?mNew),
    HGx : mem_grows (mrestrict (w_H Wx) mOld) (mrestrict (w_H Wx) ?mNew) |- _ =>
    let UNk := fresh "UNk" in
    pose proof (kept_of_frame (segs := sg) Ex rsx (w_H Wx) mOld mNew Zs HFrx
      ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
            repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                    rewrite ?Up in HrrW; unfold Zs; lia|]); destruct HinW)) as UNk;
    let UN' := fresh "UN" in
    assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview sg (w_H Wx) mNew a = aview sg (w_H Wx) m0 a)
      by (intros a Ha Hn; rewrite (UNk a Ha Hn); exact (UN a Ha Hn));
    let GR' := fresh "GR" in
    assert (GR' : mem_grows (mrestrict (w_H Wx) m0) (mrestrict (w_H Wx) mNew)) by exact (mem_grows_trans _ _ _ GR HGx);
    clear UN GR UNk HFrx HGx; rename UN' into UN; rename GR' into GR;
    try match goal with HFx : forall x : word, _ -> mNew x = mOld x |- _ => clear HFx end
  end end.

Theorem to_u16 : to_mal_obl SK B MT CTX -> to_u16_obl SK B MT CTX.
Proof.
intros MAL cx ms3 md3 HPX
  (c0 & c1 & inp & adv & Hpc & HC & HI & Hadv & Hadvc & Hadv3 & Hb0 & R10 & R12 & R14 & R15 & R21 & R16 & R11 & P0 & P8).
pose proof HC as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ3 & Hfd & Hfs & R2 & R8 & R20 & RU & SV & UN & PR & WP & BP & VO & BO).
pose proof HI as (Hc0 & Hc1 & Hc0r & Hc1r & Hinp & Hlen).
pose proof HPX as (HA & _).
pose proof HA as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
pose proof (to_win SK B MT CTX cx HPX) as (Hceil & H47 & _ & HSTK & Hsp0).
pose proof (to_pre_happ SK B MT CTX cx HPX) as (HAp & HAo).
pose proof (to_pre_P SK B MT CTX cx HPX) as
  (c0' & c1' & inp' & Hc0' & Hc1' & Hc0r' & Hc1r' & Hbufp & Hp8 & Hrap & _ & Hafp & Hbufo & Hrao & _ & _ & Hafo & Hapo
   & Haep & Hinp' & Hlen' & Hrai & Hpos & Hvis & Hword & HraT & HapT & HaoT & HentT & HTR).
pose proof (mw_au64_det SEGS _ _ _ _ Hc0' Hc0 Hc0r' Hc0r) as ->.
pose proof (mw_au64_det SEGS _ _ _ _ Hc1' Hc1 Hc1r' Hc1r) as ->.
clear Hc0' Hc1' Hc0r' Hc1r'.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : TEXT_OF_AK = 16448) by reflexivity.
set (regs := to_regs cx) in *. set (W := to_W cx) in *. set (memc := to_memc cx) in *.
change (to_p cx) with (aarg regs 0) in *. change (to_o cx) with (aarg regs 1) in *.
set (p := aarg regs 0) in *. set (o := aarg regs 1) in *.
change (to_sp cx) with (spZ regs) in *. change (to_m0 cx) with (rdW W memc) in *.
destruct (Hpos ltac:(lia)) as (Hhull & Ham & Hafi & Hapip & Hapio & Hio).
unfold amem_range in HAp, HAo.
assert (Hp0 : 0 <= p < 2 ^ 64) by (unfold p, to_p, aarg, argZ; apply bv_unsigned_in_range).
assert (HCB : 0 <= c0 /\ c0 + c1 <= 2 ^ 47 - 1)
  by (clear - Ham Hc0r; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
(* the cut's state *)
assert (Hms3 : restrict (w_H W) ms3 =
   mkst (ms_regs ms3) (Z_to_bv 64 (BASE + TO_CUT_U16)) (rdW W (ms_mem ms3)) (seg_rom SEGS)).
{ rewrite (tu_ms_eta ms3 Hfr Hsv Hrv Hfc) at 1. rewrite Hpc, Hrom. rewrite restrict_mkst_fx. reflexivity. }
set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (c0 + adv); Z_to_bv 64 (c1 - adv)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat ->
          ew E n = getr (ms_regs ms3) r)
  by (intros n r Hr Hn; subst E; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 (c0 + adv); Z_to_bv 64 (c1 - adv)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 64)
  by (rewrite (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)), R2; unfold w64, TO_FRAME;
      apply unsigned_lit_small; change TEXT_OF_AK with 16448 in *; lia).
assert (U12 : bv_unsigned (ew E 12) = p)
  by (rewrite (ER 12%nat 12%bv eq_refl ltac:(unfold A_TEXT; lia)), R12; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (ER 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)), R20; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U16 : bv_unsigned (ew E 16) = (if 2 <=? adv then bz inp 1 else 0))
  by (rewrite (ER 16%nat 16%bv eq_refl ltac:(unfold A_TEXT; lia)), R16; unfold w64; apply unsigned_lit_small;
      destruct (2 <=? adv); [pose proof (bz_rng inp 1) | ]; lia).
assert (U11 : bv_unsigned (ew E 11) = (if adv =? 3 then bz inp 2 else 0))
  by (rewrite (ER 11%nat 11%bv eq_refl ltac:(unfold A_TEXT; lia)), R11; unfold w64; apply unsigned_lit_small;
      destruct (adv =? 3); [pose proof (bz_rng inp 2) | ]; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (c0 + adv)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (c1 - adv)) by exact (EX 1%nat ltac:(lia)).
assert (HS : st_ok_pi SEGS VAL E tu_ss (restrict (w_H W) ms3)).
{ rewrite Hms3. unfold tu_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tu_rP.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U12.
    destruct BP as (jk & Hjk & (Hb0' & Hb1' & _) & Hwr). rewrite Hjk in Hb1', Hwr.
    split; [lia|]. split; [lia|]. split; [intros o' Ho'; exact (Hwr o' Ho')|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS _ _ p 0 8 (SOff 32 0) (c0 + adv));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact P0.
    + apply (chunk_ok_val SEGS _ _ p 8 8 (SOff 33 0) (c1 - adv));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
      exact P8.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I]. cbn [tu_fA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U20, U12, U16, U11. rewrite E32, E33, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    pose proof (bz_rng inp 1). pose proof (bz_rng inp 2).
    assert (Hs64 : (spZ regs - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
    change TEXT_OF_AK with 16448 in *.
    repeat match goal with |- _ /\ _ => split end;
      first [exact I | exact Hs64 | exact Hp8 | lia | destruct (2 <=? adv); lia | destruct (adv =? 3); lia]. }
assert (SHOK : sh_ok SEGS TUBx tu_SH E (rdW W (ms_mem ms3))).
{ unfold tu_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart; cbn [she_m she_lo she_hi].
  unfold TUBx; rewrite !lf_U_reg, U20, U12; cbn [Z.min Z.max]; rewrite ?Z.add_0_r, ?Z.sub_0_r.
  split.
  - intros x Hx. destruct (Hrap x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    pose proof (tu_shadow_rng p 16 x ltac:(lia) HAp Hx) as Hsx.
    unfold rd_of. rewrite (mbyte_of_aview_eq SEGS _ _ _ _ _ _ (UN (shadow_of_addr SHADOW_OFF x)
      ltac:(lia) (to_low_not_win SK B MT CTX cx (shadow_of_addr SHADOW_OFF x) HPX ltac:(lia))
      (to_E_not_shadow cx _ (to_pre_happ SK B MT CTX cx HPX) Hsx))).
    exact Hs.
  - intros a Ha. unfold SHADOW_OFF. lia. }
(* the cut's registers the code reads as addresses: a0 = p + 8, a4 / a5 the shadow addresses of p + 8 / p, s5 that
   of o (s0 = o) *)
assert (U8 : bv_unsigned (ew E 8) = o)
  by (rewrite (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)), R8; unfold w64; apply unsigned_lit_small;
      unfold o, aarg, argZ; apply bv_unsigned_in_range).
assert (Ho0 : 0 <= o < 2 ^ 64) by (unfold o, aarg, argZ; apply bv_unsigned_in_range).
Ltac tu_setreg HS r e prf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    let HS2 := fresh "HS2" in
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx r e HS eq_refl ltac:(cbn [ms_regs restrict]; prf)) as HS2;
    clear HS; rename HS2 into HS; norm_pi HS end.
tu_setreg HS (10%bv : bv 5) (SOff 12 8) ltac:(cbn [sv_denot]; rewrite U12, R10; reflexivity).
tu_setreg HS (14%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 12 8) (SLit 3)) (SOff 20 0))
  ltac:(rewrite (tu_shadow_sv E 12 8 p 20 U12 ltac:(lia) U20), R14; reflexivity).
tu_setreg HS (15%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 12 0) (SLit 3)) (SOff 20 0))
  ltac:(rewrite (tu_shadow_sv E 12 0 p 20 U12 ltac:(lia) U20), R15, Z.add_0_r; reflexivity).
tu_setreg HS (21%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 20 0))
  ltac:(rewrite (tu_shadow_sv E 8 0 o 20 U8 ltac:(lia) U20), R21, Z.add_0_r; reflexivity).
pose (RUN := paj_run_x SK B LAWS (to_G cx) HGok (to_XO cx) (to_OUT cx)).
pose proof (paj_branch (PI := PI)) as BR.
change (to_wr cx) with [(p, p + 16); (o, o + 8)] in Hajw.
set (Zp := fun a : Z => p <= a < p + 16 \/ spZ regs - 64 - 4096 <= a < spZ regs - 64).
assert (UNr : forall a, 0 <= a < 2 ^ 64 -> ~ Zp a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
  by reflexivity.
assert (GRr : mem_grows (rdW W (ms_mem ms3)) (rdW W (ms_mem ms3))) by apply mem_grows_refl.
assert (V32 : bv_unsigned (ew E 32) = c0 + adv) by (rewrite E32; apply unsigned_lit_small; lia).
assert (V33 : bv_unsigned (ew E 33) = c1 - adv) by (rewrite E33; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJ3 SHOK Bspan; [tu_awr Hajw U12 |].
tu_fold UNr GRr Zp U12.
pose proof (bz_rng inp 1) as Hb1. pose proof (bz_rng inp 2) as Hb2.
destruct (tu_want_val E _ _ U16 U11 ltac:(destruct (2 <=? adv); lia) ltac:(destruct (adv =? 3); lia)) as (Uwant & Uv).
set (vv := (if 2 <=? adv then bz inp 1 else 0) + 256 * (if adv =? 3 then bz inp 2 else 0)) in Uwant, Uv.
assert (Urem : U E (SOff 33 0) = c1 - adv) by (unfold U; rewrite (to_sv_off E 33 (c1 - adv) 0 E33 ltac:(lia) ltac:(lia)); lia).
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* want < rem: n := want *)
  rewrite branch_ltu_U in Hc. fold tu_v in Hc. fold tu_want in Hc. rewrite Uwant, Urem in Hc. apply Z.ltb_lt in Hc.
  set (nA := vv mod 320) in Uwant, Hc.
  assert (HnA : 0 <= nA < 320) by (unfold nA; apply Z.mod_pos_bound; lia).
  paj_run_tok RUN HS HJ3 SHOK Bspan; [tu_awr Hajw U12 |].
  tu_fold UNr GRr Zp U12.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { (* rem = 0: n = 0, k = 0 *)
    lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HBn end.
    rewrite branch_eq_U in HBn. fold tu_v in HBn. fold tu_want in HBn. rewrite Uwant, U_SLit in HBn.
    change (zcanon 0) with 0 in HBn. apply Z.eqb_eq in HBn.
    paj_run_tok RUN HS HJ3 SHOK Bspan; [tu_awr Hajw U12 |].
    tu_fold UNr GRr Zp U12.
    pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20.
    to_reg_raw_st HS (10%bv : bv 5) Q10. to_reg_raw_st HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
    to_reg_raw_st HS (21%bv : bv 5) Q21. sregion HS 0%nat HRp.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
      apply (MAL cx msF mdF HPX); eapply (tu_gi_mal_of cx ms3 msF md3 mdF c0 c1 inp adv 0 0 _ Zp HPX HC HI Hms) end.
    - destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & HpcF). exact HpcF.
    - refine (eq_trans Q1 _). unfold w64, TO_MAL_RA, AF_text_of. f_equal; lia.
    - exact HJ3.
    - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
    - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
    - refine (eq_trans Q2 _). exact (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)).
    - refine (eq_trans Q8 _). exact (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)).
    - refine (eq_trans Q20 _). exact (ER 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)).
    - intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [ lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
            let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; refine (eq_trans Q _);
            let nn := eval vm_compute in (Z.to_nat c) in
            exact (ER nn (Z_to_bv 5 c) eq_refl ltac:(unfold A_TEXT; lia)) end
        | ]).
      destruct Hr.
    - intros a [Ha | Ha]; [right; exact Ha | left; change (to_sp cx) with (spZ regs); change TEXT_OF_AK with 16448; unfold TO_FRAME; lia].
    - exact UNr.
    - exact GRr.
    - exact Hadv.
    - lia.
    - lia.
    - lia.
    - cbn [Z.to_nat firstn In]. tauto.
    - refine (eq_trans Q10 _). tu_regv E Uwant Uwant V32 V33. rewrite ?Z.mod_small by lia. lia.
    - refine (eq_trans Q9 _). tu_regv E Uwant Uwant V32 V33. rewrite ?Z.mod_small by lia. lia.
    - refine (eq_trans Q18 _). rewrite E32. reflexivity.
    - refine (eq_trans Q21 _). rewrite (tu_shadow_sv E 8 0 o 20 U8 ltac:(lia) U20), Z.add_0_r. reflexivity.
    - pose proof (to_word_of_region _ _ _ 12%nat p 0 _ HRp eq_refl U12
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
      tu_chunk V Uwant Uwant V32 V33 (c0 + adv + 0) ltac:(rewrite ?Z.mod_small by lia; lia).
    - pose proof (to_word_of_region _ _ _ 12%nat p 8 _ HRp eq_refl U12
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
      tu_chunk V Uwant Uwant V32 V33 (c1 - adv - 0) ltac:(rewrite ?Z.mod_small by lia; lia). }
  (* rem > 0: n = rem, memchr (q, 0, n) *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HBn end.
  rewrite branch_eq_U in HBn. fold tu_v in HBn. fold tu_want in HBn. rewrite Uwant, U_SLit in HBn.
  change (zcanon 0) with 0 in HBn. apply Z.eqb_neq in HBn.
  paj_run_tok RUN HS HJ3 SHOK Bspan; [tu_awr Hajw U12 |].
  tu_fold UNr GRr Zp U12.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. to_reg_raw_st HS (12%bv : bv 5) Q12.
  assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 64) by (unfold spZ at 1; rewrite Q2; exact U2).
  (* the shadow, the input and memchr's constants at the call are the call's *)
  assert (HnZsh : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> ~ Zp a).
  { intros a Ha Hz. unfold Zp in Hz. change TEXT_OF_AK with 16448 in Hceil.
    clear - Ha Hz HAp Hceil C1a. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  assert (KSm : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 ->
            aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
  { intros a Ha. rewrite UNr; [| unfold SHADOW_OFF in Ha; lia | exact (HnZsh a Ha)].
    apply UN; [unfold SHADOW_OFF in Ha; lia | | exact (to_E_not_shadow cx a (to_pre_happ SK B MT CTX cx HPX) Ha)].
    change TEXT_OF_AK with 16448 in *. unfold SHADOW_OFF in Ha. lia. }
  assert (KIm : forall a, c0 <= a < c0 + c1 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
  { intros a Ha. pose proof (to_nZ_in (spZ regs) p o c0 c1 a Hafi Hapip Hapio Ha) as Hn.
    rewrite UNr; [| lia | unfold Zp; change TEXT_OF_AK with 16448 in Hafi; unfold apart_frame in Hafi; lia].
    apply UN; [lia | change TEXT_OF_AK with 16448 in Hafi; unfold apart_frame in Hafi; lia |].
    intros (r & Hin & Hr). apply Hn. change (to_wr cx) with [(p, p + 16); (o, o + 8)] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia. }
  assert (KRm : forall a, 0x10360 <= a < 0x10380 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
  { intros a Ha. destruct (MC_RO a Ha) as (HrmA & _ & _).
    assert (HnE : ~ to_E cx a) by (intros HE; exact (Hro a HE (or_introl HrmA))).
    assert (HnP : ~ (p <= a < p + 16)).
    { intros Hp. apply HnE. exists (p, p + 16). split; [left; reflexivity | cbn [fst snd]; lia]. }
    change TEXT_OF_AK with 16448 in Hceil.
    rewrite UNr; [| lia | unfold Zp; lia]. apply UN; [lia | lia | exact HnE]. }
  eapply SRr_bind.
  { eapply (aj_gx_memchrM_at SK SEGS B LAWS pa_segs_low 0x10360 0x10380 _ MEMCHR (to_G cx) (to_XO cx) (to_OUT cx) W
      (ms_regs ms1) (ms_mem ms1) (to_STK cx) (to_sp0 cx) (to_FP cx) (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx)
      (to_md0 cx) (to_own cx) (to_lyc cx) (to_Sc cx) _ (to_k cx) (c0 + adv) 0 nA _ HGok HJ3).
    - rewrite Usp1. rewrite Zminus_mod, Hal16. reflexivity.
    - rewrite Usp1. change ESTACK with 4096. change TEXT_OF_AK with 16448 in HSTK. lia.
    - rewrite Usp1. lia.
    - rewrite Q3, (ER 3%nat 3%bv eq_refl ltac:(unfold A_TEXT; lia)). refine (eq_trans (RU 3 ltac:(cbv; tauto)) _). exact Hgp.
    - rewrite Q4, (ER 4%nat 4%bv eq_refl ltac:(unfold A_TEXT; lia)). refine (eq_trans (RU 4 ltac:(cbv; tauto)) _). exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q10, E32. reflexivity.
    - rewrite Q11. reflexivity.
    - refine (eq_trans Q12 _). tu_regv E Uwant Uwant V32 V33. rewrite ?Z.mod_small by lia. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros a Ha. rewrite Usp1. change ESTACK with 4096. split.
      + rewrite KIm by lia. rewrite <- (ard_aview SEGS). unfold ard.
        destruct Hinp as (_ & _ & Hab). replace a with (c0 + Z.of_nat (Z.to_nat (a - c0))) by lia.
        rewrite (Hab (Z.to_nat (a - c0)) ltac:(lia)).
        rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by lia. discriminate.
      + change TEXT_OF_AK with 16448 in Hafi. unfold apart_frame in Hafi. lia.
    - clear - Ham Hadv Hc HnA. unfold amem_range in *. lia.
    - apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply Hrai; lia|].
      intros x Hx. rewrite (ard_aview SEGS). apply KSm. clear - Hx HCB Hadv Hadvc Hc HnA HBn. unfold shadow_addr, SHADOW_OFF.
      assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
    - intros Hn0 s0 Hs0. rewrite KSm; [rewrite <- (ard_aview SEGS); apply Hhull | ].
      + clear - Hs0 HCB Hadv Hadvc Hc HnA HBn. unfold shadow_addr in *.
        assert ((SHADOW_OFF + c0 / 8) / 8 * 8 <= (SHADOW_OFF + (c0 + adv) / 8) / 8 * 8).
        { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
          assert (c0 / 8 <= (c0 + adv) / 8) by (apply Z.div_le_mono; lia). lia. }
        assert ((SHADOW_OFF + (c0 + adv + nA - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (c0 + c1 - 1) / 8) / 8 * 8).
        { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
          assert ((c0 + adv + nA - 1) / 8 <= (c0 + c1 - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
        lia.
      + clear - Hs0 HCB Hadv Hadvc Hc HnA HBn. unfold shadow_addr, SHADOW_OFF in *.
        assert (0 <= (c0 + adv) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        assert (0 <= (c0 + adv + nA - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        lia.
    - apply (consts_view_keep SEGS 0x10360 0x10380 W memc).
      + exact (aconsts_of_aro SEGS B _ _ W memc 0x10360 0x10380 MC_RO HROD).
      + exact KRm. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ4 & HP4 & (kk & Hfb & H10) & Hkeep & Hpres2 & Hsm).
  assert (HP4' : aregs_preserved (ms_regs ms1) regs2) by exact HP4.
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP4' [0]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    unfold region_kept. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]. rewrite U12. split.
    - intros a Ha. apply (mbyte_of_aview SEGS). apply Hkeep; [lia|]. rewrite Usp1. change ESTACK with 4096.
      clear - Ha Hafp. change TEXT_OF_AK with 16448 in Hafp. unfold apart_frame in Hafp. lia.
    - intros a Ha Hw. apply (writable_kept (segs := SEGS) (w_H W) (ms_mem ms1) mem2); [intros Hp; exact (Hpres2 _ Hp) | exact Hw]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
  assert (E44 : ew E' 44 = getr regs2 10) by (rewrite HE'; reflexivity).
  assert (U12' : bv_unsigned (ew E' 12) = p) by (rewrite OLD by lia; exact U12).
  assert (U20' : bv_unsigned (ew E' 20) = SHADOW_OFF) by (rewrite OLD by lia; exact U20).
  assert (V32' : bv_unsigned (ew E' 32) = c0 + adv) by (rewrite OLD by lia; exact V32).
  assert (V33' : bv_unsigned (ew E' 33) = c1 - adv) by (rewrite OLD by lia; exact V33).
  assert (U8' : bv_unsigned (ew E' 8) = o) by (rewrite OLD by lia; exact U8).
  assert (Uwant' : U E' tu_want = nA).
  { destruct (tu_want_val E' _ _ ltac:(rewrite OLD by lia; exact U16) ltac:(rewrite OLD by lia; exact U11)
      ltac:(destruct (2 <=? adv); lia) ltac:(destruct (adv =? 3); lia)) as (UwE & _). rewrite UwE. reflexivity. }
  clear HE'.
  (* kept since the cut, outside Zp *)
  assert (UNr2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zp a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms3) a).
  { intros a Ha Hz. rewrite Hkeep; [exact (UNr a Ha Hz) | exact Ha |]. rewrite Usp1. change ESTACK with 4096.
    clear - Hz. unfold Zp in Hz. lia. }
  assert (GRr2 : mem_grows (rdW W (ms_mem ms3)) (rdW W mem2))
    by (eapply mem_grows_trans; [exact GRr | apply tu_grows_of_present; exact Hpres2]).
  clear UNr GRr. rename UNr2 into UNr. rename GRr2 into GRr.
  assert (SHOK2 : sh_ok SEGS TUBx tu_SH E' (rdW W mem2)).
  { unfold tu_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart; cbn [she_m she_lo she_hi].
    unfold TUBx; rewrite !lf_U_reg, U20', U12'; cbn [Z.min Z.max]; rewrite ?Z.add_0_r, ?Z.sub_0_r.
    split.
    - rewrite <- (aview_rd_of SEGS). apply (ra_shadow_eq (ard SEGS (rdW W memc))); [exact Hrap|].
      intros x Hx. rewrite (ard_aview SEGS).
      assert (Hsx : SHADOW_OFF <= shadow_addr x < SHADOW_OFF + 2 ^ 44).
      { clear - Hx HAp Hp0. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
        assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
      rewrite Hkeep; [exact (KSm _ Hsx) | unfold SHADOW_OFF in Hsx; lia |]. rewrite Usp1. change ESTACK with 4096.
      change TEXT_OF_AK with 16448 in Hceil. clear - Hsx Hceil C1a. unfold SHADOW_OFF in Hsx. lia.
    - intros a Ha. clear - Ha HAp. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  clear SHOK. rename SHOK2 into SHOK.
  paj_run_tok RUN HS HJ4 SHOK Bspan; [tu_awr Hajw U12' |].
  tu_fold UNr GRr Zp U12'.
  destruct Hfb as (Hkk0 & Hkkb & Hkkn).
  assert (Ua0 : U E' (SOff 44 0) = if kk <? nA then c0 + adv + kk else 0).
  { unfold U. cbn [sv_denot]. rewrite E44, H10, Z.add_0_r, Z_to_bv_bv_unsigned.
    destruct (kk <? nA); unfold w64; apply unsigned_lit_small; lia. }
  (* the bytes memchr read, at the call, are the input's *)
  assert (HNZ : forall i, 0 <= i < kk -> exists b, ard SEGS (rdW W memc) (c0 + adv + i) = Some b /\ b <> 0).
  { intros i Hi. destruct (Hkkb i Hi) as (b & Hb & Hbz). exists b. split; [|exact Hbz].
    rewrite (ard_aview SEGS), <- KIm by lia. exact Hb. }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { (* a0 = 0: no NUL among the n bytes, k = n *)
    lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB0 end.
    rewrite branch_eq_U, Ua0, U_SLit in HB0. change (zcanon 0) with 0 in HB0. apply Z.eqb_eq in HB0.
    assert (Hkk : kk = nA) by (destruct (Z.ltb_spec kk nA); lia).
    paj_run_tok RUN HS HJ4 SHOK Bspan; [tu_awr Hajw U12' |].
    tu_fold UNr GRr Zp U12'.
    pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
    prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (8%bv : bv 5) F8. prreg HS (20%bv : bv 5) F20.
    prreg HS (18%bv : bv 5) F18.
    to_reg_raw_st HS (21%bv : bv 5) F21. to_reg_raw_st HS (10%bv : bv 5) F10. to_reg_raw_st HS (9%bv : bv 5) F9.
    sregion HS 0%nat HRp.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
      apply (MAL cx msF mdF HPX); eapply (tu_gi_mal_of cx ms3 msF md3 mdF c0 c1 inp adv nA nA _ Zp HPX HC HI Hms) end.
    - destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & HpcF). exact HpcF.
    - refine (eq_trans F1 _). unfold w64, TO_MAL_RA, AF_text_of. f_equal; lia.
    - exact HJ4.
    - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite (proj1 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
    - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite (proj2 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
    - refine (eq_trans F2 _). exact (eq_trans (OLD 2%nat ltac:(lia)) (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia))).
    - refine (eq_trans F8 _). exact (eq_trans (OLD 8%nat ltac:(lia)) (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia))).
    - refine (eq_trans F20 _). exact (eq_trans (OLD 20%nat ltac:(lia)) (ER 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia))).
    - intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [ lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
            let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; refine (eq_trans Q _);
            let nn := eval vm_compute in (Z.to_nat c) in
            exact (eq_trans (OLD nn ltac:(lia)) (ER nn (Z_to_bv 5 c) eq_refl ltac:(unfold A_TEXT; lia))) end
        | ]).
      destruct Hr.
    - intros a [Ha | Ha]; [right; exact Ha | left; change (to_sp cx) with (spZ regs); change TEXT_OF_AK with 16448; unfold TO_FRAME; lia].
    - exact UNr.
    - exact GRr.
    - exact Hadv.
    - lia.
    - lia.
    - pose proof (Z.mod_pos_bound vv 320 ltac:(lia)). lia.
    - exact (tu_nul_free (rdW W memc) c0 inp adv nA Hinp ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(intros i Hi; apply HNZ; lia)).
    - refine (eq_trans F10 _). tu_regv E' Uwant' Uwant' V32' V33'. rewrite ?Z.mod_small by lia. lia.
    - refine (eq_trans F9 _). tu_regv E' Uwant' Uwant' V32' V33'. rewrite ?Z.mod_small by lia. lia.
    - refine (eq_trans F18 _). rewrite (OLD 32%nat ltac:(lia)), E32. reflexivity.
    - refine (eq_trans F21 _). rewrite (tu_shadow_sv E' 8 0 o 20 U8' ltac:(lia) U20'), Z.add_0_r. reflexivity.
    - pose proof (to_word_of_region _ _ _ 12%nat p 0 _ HRp eq_refl U12'
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
      tu_chunk V Uwant' Uwant' V32' V33' (c0 + adv + nA) ltac:(rewrite ?Z.mod_small by lia; lia).
    - pose proof (to_word_of_region _ _ _ 12%nat p 8 _ HRp eq_refl U12'
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
      tu_chunk V Uwant' Uwant' V32' V33' (c1 - adv - nA) ltac:(rewrite ?Z.mod_small by lia; lia). }
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB0 end.
  rewrite branch_eq_U, Ua0, U_SLit in HB0. change (zcanon 0) with 0 in HB0. apply Z.eqb_neq in HB0.
  assert (Hkk : kk < nA) by (destruct (Z.ltb_spec kk nA); lia).
  rewrite (proj2 (Z.ltb_lt _ _) Hkk) in Ua0.
  paj_run_tok RUN HS HJ4 SHOK Bspan; [tu_awr Hajw U12' |].
  tu_fold UNr GRr Zp U12'.
  { pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
    prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (8%bv : bv 5) F8. prreg HS (20%bv : bv 5) F20.
    prreg HS (18%bv : bv 5) F18.
    to_reg_raw_st HS (21%bv : bv 5) F21. to_reg_raw_st HS (10%bv : bv 5) F10. to_reg_raw_st HS (9%bv : bv 5) F9.
    sregion HS 0%nat HRp.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
      apply (MAL cx msF mdF HPX); eapply (tu_gi_mal_of cx ms3 msF md3 mdF c0 c1 inp adv nA kk _ Zp HPX HC HI Hms) end.
    - destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & HpcF). exact HpcF.
    - refine (eq_trans F1 _). unfold w64, TO_MAL_RA, AF_text_of. f_equal; lia.
    - exact HJ4.
    - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite (proj1 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
    - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite (proj2 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
    - refine (eq_trans F2 _). exact (eq_trans (OLD 2%nat ltac:(lia)) (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia))).
    - refine (eq_trans F8 _). exact (eq_trans (OLD 8%nat ltac:(lia)) (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia))).
    - refine (eq_trans F20 _). exact (eq_trans (OLD 20%nat ltac:(lia)) (ER 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia))).
    - intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [ lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
            let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; refine (eq_trans Q _);
            let nn := eval vm_compute in (Z.to_nat c) in
            exact (eq_trans (OLD nn ltac:(lia)) (ER nn (Z_to_bv 5 c) eq_refl ltac:(unfold A_TEXT; lia))) end
        | ]).
      destruct Hr.
    - intros a [Ha | Ha]; [right; exact Ha | left; change (to_sp cx) with (spZ regs); change TEXT_OF_AK with 16448; unfold TO_FRAME; lia].
    - exact UNr.
    - exact GRr.
    - exact Hadv.
    - lia.
    - lia.
    - pose proof (Z.mod_pos_bound vv 320 ltac:(lia)). lia.
    - exact (tu_nul_free (rdW W memc) c0 inp adv kk Hinp ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(intros i Hi; apply HNZ; lia)).
    - refine (eq_trans F10 _). rewrite (denot_lit_U E'). unfold w64. f_equal.
      repeat first [rewrite Ua0 | rewrite U_SAlu | rewrite U_SMd | rewrite U_SOff | rewrite U_SLit].
      cbn [zalu_raw zmd_raw]. rewrite V32'. unfold zcanon, M64. clear - Hkk Hkk0 HCB Hadv. rewrite ?Z.add_0_r. lia.
    - refine (eq_trans F9 _). rewrite (denot_lit_U E'). unfold w64. f_equal.
      repeat first [rewrite Ua0 | rewrite U_SAlu | rewrite U_SMd | rewrite U_SOff | rewrite U_SLit].
      cbn [zalu_raw zmd_raw]. rewrite V32'. unfold zcanon, M64. clear - Hkk Hkk0 HCB Hadv. rewrite ?Z.add_0_r. lia.
    - refine (eq_trans F18 _). rewrite (OLD 32%nat ltac:(lia)), E32. reflexivity.
    - refine (eq_trans F21 _). rewrite (tu_shadow_sv E' 8 0 o 20 U8' ltac:(lia) U20'), Z.add_0_r. reflexivity.
    - pose proof (to_word_of_region _ _ _ 12%nat p 0 _ HRp eq_refl U12'
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
      tu_chunk V Uwant' Uwant' V32' V33' (c0 + adv + nA) ltac:(rewrite ?Z.mod_small by lia; lia).
    - pose proof (to_word_of_region _ _ _ 12%nat p 8 _ HRp eq_refl U12'
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
      tu_chunk V Uwant' Uwant' V32' V33' (c1 - adv - nA) ltac:(rewrite ?Z.mod_small by lia; lia). } }
(* want >= rem: n := rem *)
rewrite branch_ltu_U in Hc. fold tu_v in Hc. fold tu_want in Hc. rewrite Uwant, Urem in Hc. apply Z.ltb_ge in Hc.
paj_run_tok RUN HS HJ3 SHOK Bspan; [tu_awr Hajw U12 |].
tu_fold UNr GRr Zp U12.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* rem = 0: n = 0, k = 0 *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HBn end.
  rewrite (to_beqz_off E 33 (c1 - adv) 0 E33 ltac:(lia) ltac:(lia)) in HBn. apply Z.eqb_eq in HBn.
  paj_run_tok RUN HS HJ3 SHOK Bspan; [tu_awr Hajw U12 |].
  tu_fold UNr GRr Zp U12.
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20.
  prreg HS (10%bv : bv 5) Q10. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  to_reg_raw_st HS (21%bv : bv 5) Q21. sregion HS 0%nat HRp.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
    apply (MAL cx msF mdF HPX); eapply (tu_gi_mal_of cx ms3 msF md3 mdF c0 c1 inp adv 0 0 _ Zp HPX HC HI Hms) end.
  - destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & HpcF). exact HpcF.
  - refine (eq_trans Q1 _). unfold w64, TO_MAL_RA, AF_text_of. f_equal; lia.
  - exact HJ3.
  - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
  - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
  - refine (eq_trans Q2 _). exact (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)).
  - refine (eq_trans Q8 _). exact (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)).
  - refine (eq_trans Q20 _). exact (ER 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)).
  - intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
          let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; refine (eq_trans Q _);
          let nn := eval vm_compute in (Z.to_nat c) in
          exact (ER nn (Z_to_bv 5 c) eq_refl ltac:(unfold A_TEXT; lia)) end
      | ]).
    destruct Hr.
  - intros a [Ha | Ha]; [right; exact Ha | left; change (to_sp cx) with (spZ regs); change TEXT_OF_AK with 16448; unfold TO_FRAME; lia].
  - exact UNr.
  - exact GRr.
  - exact Hadv.
  - lia.
  - lia.
  - lia.
  - cbn [Z.to_nat firstn In]. tauto.
  - refine (eq_trans Q10 _). rewrite V33. unfold w64. f_equal; lia.
  - refine (eq_trans Q9 _). rewrite E33. unfold w64. f_equal; lia.
  - refine (eq_trans Q18 _). rewrite E32. reflexivity.
  - refine (eq_trans Q21 _). rewrite (tu_shadow_sv E 8 0 o 20 U8 ltac:(lia) U20), Z.add_0_r. reflexivity.
  - pose proof (to_word_of_region _ _ _ 12%nat p 0 _ HRp eq_refl U12
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
    assert (Hv : bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))) = c0 + adv + 0)
      by (tu_uval V32 V33; rewrite !Z.mod_small by lia; lia).
    rewrite Hv in V. exact V.
  - pose proof (to_word_of_region _ _ _ 12%nat p 8 _ HRp eq_refl U12
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
    assert (Hv : bv_unsigned (sv_denot E (SLit 0)) = c1 - adv - 0) by (tu_uval V32 V33; rewrite ?Z.mod_small by lia; lia).
    rewrite Hv in V. exact V. }
(* rem > 0: n = rem, memchr (q, 0, n) *)
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HBn end.
rewrite (to_beqz_off E 33 (c1 - adv) 0 E33 ltac:(lia) ltac:(lia)) in HBn. apply Z.eqb_neq in HBn.
paj_run_tok RUN HS HJ3 SHOK Bspan; [tu_awr Hajw U12 |].
tu_fold UNr GRr Zp U12.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 64) by (unfold spZ at 1; rewrite Q2; exact U2).
(* the shadow, the input and memchr's constants at the call are the call's *)
assert (HnZsh : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> ~ Zp a).
{ intros a Ha Hz. unfold Zp in Hz. change TEXT_OF_AK with 16448 in Hceil.
  clear - Ha Hz HAp Hceil C1a. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
assert (KSm : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 ->
          aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite UNr; [| unfold SHADOW_OFF in Ha; lia | exact (HnZsh a Ha)].
  apply UN; [unfold SHADOW_OFF in Ha; lia | | exact (to_E_not_shadow cx a (to_pre_happ SK B MT CTX cx HPX) Ha)].
  change TEXT_OF_AK with 16448 in *. unfold SHADOW_OFF in Ha. lia. }
assert (KIm : forall a, c0 <= a < c0 + c1 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. pose proof (to_nZ_in (spZ regs) p o c0 c1 a Hafi Hapip Hapio Ha) as Hn.
  rewrite UNr; [| lia | unfold Zp; change TEXT_OF_AK with 16448 in Hafi; unfold apart_frame in Hafi; lia].
  apply UN; [lia | change TEXT_OF_AK with 16448 in Hafi; unfold apart_frame in Hafi; lia |].
  intros (r & Hin & Hr). apply Hn. change (to_wr cx) with [(p, p + 16); (o, o + 8)] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia. }
assert (KRm : forall a, 0x10360 <= a < 0x10380 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. destruct (MC_RO a Ha) as (HrmA & _ & _).
  assert (HnE : ~ to_E cx a) by (intros HE; exact (Hro a HE (or_introl HrmA))).
  assert (HnP : ~ (p <= a < p + 16)).
  { intros Hp. apply HnE. exists (p, p + 16). split; [left; reflexivity | cbn [fst snd]; lia]. }
  change TEXT_OF_AK with 16448 in Hceil.
  rewrite UNr; [| lia | unfold Zp; lia]. apply UN; [lia | lia | exact HnE]. }
eapply SRr_bind.
{ eapply (aj_gx_memchrM_at SK SEGS B LAWS pa_segs_low 0x10360 0x10380 _ MEMCHR (to_G cx) (to_XO cx) (to_OUT cx) W
    (ms_regs ms1) (ms_mem ms1) (to_STK cx) (to_sp0 cx) (to_FP cx) (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx)
    (to_md0 cx) (to_own cx) (to_lyc cx) (to_Sc cx) _ (to_k cx) (c0 + adv) 0 (c1 - adv) _ HGok HJ3).
  - rewrite Usp1. rewrite Zminus_mod, Hal16. reflexivity.
  - rewrite Usp1. change ESTACK with 4096. change TEXT_OF_AK with 16448 in HSTK. lia.
  - rewrite Usp1. lia.
  - rewrite Q3, (ER 3%nat 3%bv eq_refl ltac:(unfold A_TEXT; lia)). refine (eq_trans (RU 3 ltac:(cbv; tauto)) _). exact Hgp.
  - rewrite Q4, (ER 4%nat 4%bv eq_refl ltac:(unfold A_TEXT; lia)). refine (eq_trans (RU 4 ltac:(cbv; tauto)) _). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q10, E32. reflexivity.
  - rewrite Q11. reflexivity.
  - rewrite Q12, E33. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros a Ha. rewrite Usp1. change ESTACK with 4096. split.
    + rewrite KIm by lia. rewrite <- (ard_aview SEGS). unfold ard.
      destruct Hinp as (_ & _ & Hab). replace a with (c0 + Z.of_nat (Z.to_nat (a - c0))) by lia.
      rewrite (Hab (Z.to_nat (a - c0)) ltac:(lia)).
      rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by lia. discriminate.
    + change TEXT_OF_AK with 16448 in Hafi. unfold apart_frame in Hafi. lia.
  - clear - Ham Hadv. unfold amem_range in *. lia.
  - apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply Hrai; lia|].
    intros x Hx. rewrite (ard_aview SEGS). apply KSm. clear - Hx HCB Hadv Hadvc. unfold shadow_addr, SHADOW_OFF.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
  - intros Hn0 s0 Hs0. rewrite KSm; [rewrite <- (ard_aview SEGS); apply Hhull | ].
    + clear - Hs0 HCB Hadv Hadvc. unfold shadow_addr in *.
      assert ((SHADOW_OFF + c0 / 8) / 8 * 8 <= (SHADOW_OFF + (c0 + adv) / 8) / 8 * 8).
      { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
        assert (c0 / 8 <= (c0 + adv) / 8) by (apply Z.div_le_mono; lia). lia. }
      replace (c0 + adv + (c1 - adv) - 1) with (c0 + c1 - 1) in Hs0 by lia. lia.
    + clear - Hs0 HCB Hadv Hadvc. unfold shadow_addr, SHADOW_OFF in *.
      assert (0 <= (c0 + adv) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      assert (0 <= (c0 + adv + (c1 - adv) - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      lia.
  - apply (consts_view_keep SEGS 0x10360 0x10380 W memc).
    + exact (aconsts_of_aro SEGS B _ _ W memc 0x10360 0x10380 MC_RO HROD).
    + exact KRm. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ4 & HP4 & (kk & Hfb & H10) & Hkeep & Hpres2 & Hsm).
assert (HP4' : aregs_preserved (ms_regs ms1) regs2) by exact HP4.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP4' [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  unfold region_kept. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]. rewrite U12. split.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hkeep; [lia|]. rewrite Usp1. change ESTACK with 4096.
    clear - Ha Hafp. change TEXT_OF_AK with 16448 in Hafp. unfold apart_frame in Hafp. lia.
  - intros a Ha Hw. apply (writable_kept (segs := SEGS) (w_H W) (ms_mem ms1) mem2); [intros Hp; exact (Hpres2 _ Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (E44 : ew E' 44 = getr regs2 10) by (rewrite HE'; reflexivity).
assert (U12' : bv_unsigned (ew E' 12) = p) by (rewrite OLD by lia; exact U12).
assert (U20' : bv_unsigned (ew E' 20) = SHADOW_OFF) by (rewrite OLD by lia; exact U20).
assert (V32' : bv_unsigned (ew E' 32) = c0 + adv) by (rewrite OLD by lia; exact V32).
assert (V33' : bv_unsigned (ew E' 33) = c1 - adv) by (rewrite OLD by lia; exact V33).
assert (U8' : bv_unsigned (ew E' 8) = o) by (rewrite OLD by lia; exact U8).
clear HE'.
(* kept since the cut, outside Zp *)
assert (UNr2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zp a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms3) a).
{ intros a Ha Hz. rewrite Hkeep; [exact (UNr a Ha Hz) | exact Ha |]. rewrite Usp1. change ESTACK with 4096.
  clear - Hz. unfold Zp in Hz. lia. }
assert (GRr2 : mem_grows (rdW W (ms_mem ms3)) (rdW W mem2))
  by (eapply mem_grows_trans; [exact GRr | apply tu_grows_of_present; exact Hpres2]).
clear UNr GRr. rename UNr2 into UNr. rename GRr2 into GRr.
assert (SHOK2 : sh_ok SEGS TUBx tu_SH E' (rdW W mem2)).
{ unfold tu_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart; cbn [she_m she_lo she_hi].
  unfold TUBx; rewrite !lf_U_reg, U20', U12'; cbn [Z.min Z.max]; rewrite ?Z.add_0_r, ?Z.sub_0_r.
  split.
  - rewrite <- (aview_rd_of SEGS). apply (ra_shadow_eq (ard SEGS (rdW W memc))); [exact Hrap|].
    intros x Hx. rewrite (ard_aview SEGS).
    assert (Hsx : SHADOW_OFF <= shadow_addr x < SHADOW_OFF + 2 ^ 44).
    { clear - Hx HAp Hp0. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
      assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
    rewrite Hkeep; [exact (KSm _ Hsx) | unfold SHADOW_OFF in Hsx; lia |]. rewrite Usp1. change ESTACK with 4096.
    change TEXT_OF_AK with 16448 in Hceil. clear - Hsx Hceil C1a. unfold SHADOW_OFF in Hsx. lia.
  - intros a Ha. clear - Ha HAp. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
clear SHOK. rename SHOK2 into SHOK.
paj_run_tok RUN HS HJ4 SHOK Bspan; [tu_awr Hajw U12' |].
tu_fold UNr GRr Zp U12'.
destruct Hfb as (Hkk0 & Hkkb & Hkkn).
assert (Ua0 : U E' (SOff 44 0) = if kk <? c1 - adv then c0 + adv + kk else 0).
{ unfold U. cbn [sv_denot]. rewrite E44, H10, Z.add_0_r, Z_to_bv_bv_unsigned.
  destruct (kk <? c1 - adv); unfold w64; apply unsigned_lit_small; lia. }
(* the bytes memchr read, at the call, are the input's *)
assert (HNZ : forall i, 0 <= i < kk -> exists b, ard SEGS (rdW W memc) (c0 + adv + i) = Some b /\ b <> 0).
{ intros i Hi. destruct (Hkkb i Hi) as (b & Hb & Hbz). exists b. split; [|exact Hbz].
  rewrite (ard_aview SEGS), <- KIm by lia. exact Hb. }
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* a0 = 0: no NUL among the n bytes, k = n *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB0 end.
  rewrite branch_eq_U, Ua0, U_SLit in HB0. change (zcanon 0) with 0 in HB0. apply Z.eqb_eq in HB0.
  assert (Hkk : kk = c1 - adv) by (destruct (Z.ltb_spec kk (c1 - adv)); lia).
  paj_run_tok RUN HS HJ4 SHOK Bspan; [tu_awr Hajw U12' |].
  tu_fold UNr GRr Zp U12'.
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (8%bv : bv 5) F8. prreg HS (20%bv : bv 5) F20.
  prreg HS (18%bv : bv 5) F18.
  to_reg_raw_st HS (21%bv : bv 5) F21. to_reg_raw_st HS (10%bv : bv 5) F10. to_reg_raw_st HS (9%bv : bv 5) F9.
  sregion HS 0%nat HRp.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
    apply (MAL cx msF mdF HPX); eapply (tu_gi_mal_of cx ms3 msF md3 mdF c0 c1 inp adv (c1 - adv) (c1 - adv) _ Zp HPX HC HI Hms) end.
  - destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & HpcF). exact HpcF.
  - refine (eq_trans F1 _). unfold w64, TO_MAL_RA, AF_text_of. f_equal; lia.
  - exact HJ4.
  - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite (proj1 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
  - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite (proj2 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
  - refine (eq_trans F2 _). exact (eq_trans (OLD 2%nat ltac:(lia)) (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia))).
  - refine (eq_trans F8 _). exact (eq_trans (OLD 8%nat ltac:(lia)) (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia))).
  - refine (eq_trans F20 _). exact (eq_trans (OLD 20%nat ltac:(lia)) (ER 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia))).
  - intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
          let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; refine (eq_trans Q _);
          let nn := eval vm_compute in (Z.to_nat c) in
          exact (eq_trans (OLD nn ltac:(lia)) (ER nn (Z_to_bv 5 c) eq_refl ltac:(unfold A_TEXT; lia))) end
      | ]).
    destruct Hr.
  - intros a [Ha | Ha]; [right; exact Ha | left; change (to_sp cx) with (spZ regs); change TEXT_OF_AK with 16448; unfold TO_FRAME; lia].
  - exact UNr.
  - exact GRr.
  - exact Hadv.
  - lia.
  - lia.
  - pose proof (Z.mod_pos_bound vv 320 ltac:(lia)). lia.
  - exact (tu_nul_free (rdW W memc) c0 inp adv (c1 - adv) Hinp ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(intros i Hi; apply HNZ; lia)).
  - refine (eq_trans F10 _). cbn [sv_denot]. rewrite (OLD 33%nat ltac:(lia)), V33. unfold w64. f_equal; lia.
  - refine (eq_trans F9 _). cbn [sv_denot]. rewrite (OLD 33%nat ltac:(lia)), V33. unfold w64. f_equal; lia.
  - refine (eq_trans F18 _). rewrite (OLD 32%nat ltac:(lia)), E32. reflexivity.
  - refine (eq_trans F21 _). rewrite (tu_shadow_sv E' 8 0 o 20 U8' ltac:(lia) U20'), Z.add_0_r. reflexivity.
  - pose proof (to_word_of_region _ _ _ 12%nat p 0 _ HRp eq_refl U12'
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
    assert (Hv : bv_unsigned (sv_denot E' (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))) = c0 + adv + (c1 - adv))
      by (tu_uval V32' V33'; rewrite !Z.mod_small by lia; lia).
    rewrite Hv in V. exact V.
  - pose proof (to_word_of_region _ _ _ 12%nat p 8 _ HRp eq_refl U12'
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
    assert (Hv : bv_unsigned (sv_denot E' (SLit 0)) = c1 - adv - (c1 - adv)) by (tu_uval V32' V33'; lia).
    rewrite Hv in V. exact V. }
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB0 end.
rewrite branch_eq_U, Ua0, U_SLit in HB0. change (zcanon 0) with 0 in HB0. apply Z.eqb_neq in HB0.
assert (Hkk : kk < c1 - adv) by (destruct (Z.ltb_spec kk (c1 - adv)); lia).
rewrite (proj2 (Z.ltb_lt _ _) Hkk) in Ua0.
paj_run_tok RUN HS HJ4 SHOK Bspan; [tu_awr Hajw U12' |].
tu_fold UNr GRr Zp U12'.
{ pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (8%bv : bv 5) F8. prreg HS (20%bv : bv 5) F20.
  prreg HS (18%bv : bv 5) F18.
  to_reg_raw_st HS (21%bv : bv 5) F21. to_reg_raw_st HS (10%bv : bv 5) F10. to_reg_raw_st HS (9%bv : bv 5) F9.
  sregion HS 0%nat HRp.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
    apply (MAL cx msF mdF HPX); eapply (tu_gi_mal_of cx ms3 msF md3 mdF c0 c1 inp adv (c1 - adv) kk _ Zp HPX HC HI Hms) end.
  - destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & HpcF). exact HpcF.
  - refine (eq_trans F1 _). unfold w64, TO_MAL_RA, AF_text_of. f_equal; lia.
  - exact HJ4.
  - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite (proj1 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
  - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite (proj2 (tu_sbm_fds _ _ Hsm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
  - refine (eq_trans F2 _). exact (eq_trans (OLD 2%nat ltac:(lia)) (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia))).
  - refine (eq_trans F8 _). exact (eq_trans (OLD 8%nat ltac:(lia)) (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia))).
  - refine (eq_trans F20 _). exact (eq_trans (OLD 20%nat ltac:(lia)) (ER 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia))).
  - intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
          let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; refine (eq_trans Q _);
          let nn := eval vm_compute in (Z.to_nat c) in
          exact (eq_trans (OLD nn ltac:(lia)) (ER nn (Z_to_bv 5 c) eq_refl ltac:(unfold A_TEXT; lia))) end
      | ]).
    destruct Hr.
  - intros a [Ha | Ha]; [right; exact Ha | left; change (to_sp cx) with (spZ regs); change TEXT_OF_AK with 16448; unfold TO_FRAME; lia].
  - exact UNr.
  - exact GRr.
  - exact Hadv.
  - lia.
  - lia.
  - pose proof (Z.mod_pos_bound vv 320 ltac:(lia)). lia.
  - exact (tu_nul_free (rdW W memc) c0 inp adv kk Hinp ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(intros i Hi; apply HNZ; lia)).
  - refine (eq_trans F10 _). rewrite (denot_lit_U E'). unfold w64. f_equal.
    repeat first [rewrite Ua0 | rewrite U_SAlu | rewrite U_SMd | rewrite U_SOff | rewrite U_SLit].
    cbn [zalu_raw zmd_raw]. rewrite V32'. unfold zcanon, M64. clear - Hkk Hkk0 HCB Hadv. rewrite ?Z.add_0_r. lia.
  - refine (eq_trans F9 _). rewrite (denot_lit_U E'). unfold w64. f_equal.
    repeat first [rewrite Ua0 | rewrite U_SAlu | rewrite U_SMd | rewrite U_SOff | rewrite U_SLit].
    cbn [zalu_raw zmd_raw]. rewrite V32'. unfold zcanon, M64. clear - Hkk Hkk0 HCB Hadv. rewrite ?Z.add_0_r. lia.
  - refine (eq_trans F18 _). rewrite (OLD 32%nat ltac:(lia)), E32. reflexivity.
  - refine (eq_trans F21 _). rewrite (tu_shadow_sv E' 8 0 o 20 U8' ltac:(lia) U20'), Z.add_0_r. reflexivity.
  - pose proof (to_word_of_region _ _ _ 12%nat p 0 _ HRp eq_refl U12'
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
    assert (Hv : bv_unsigned (sv_denot E' (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))) = c0 + adv + (c1 - adv))
      by (tu_uval V32' V33'; rewrite !Z.mod_small by lia; lia).
    rewrite Hv in V. exact V.
  - pose proof (to_word_of_region _ _ _ 12%nat p 8 _ HRp eq_refl U12'
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
    assert (Hv : bv_unsigned (sv_denot E' (SLit 0)) = c1 - adv - (c1 - adv)) by (tu_uval V32' V33'; lia).
    rewrite Hv in V. exact V. }
Qed.

About to_u16.
Print Assumptions to_u16.

End b.
End a.
