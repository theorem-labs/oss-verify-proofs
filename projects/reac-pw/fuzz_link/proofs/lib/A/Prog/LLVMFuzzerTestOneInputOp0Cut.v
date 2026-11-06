(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 198 of its 257 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputArmR.v; 289 of its 330 lines of code are new or changed and 216 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm (operation byte mod 6 = 0, +0x608 .. +0xfbc; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): the arm's own cuts.
   They are inside the arm's segment, so they are this walk's and not the interface's.

     r_d_inv i    +0xdac  the two size bytes are read (kc in s2, ac in s4, each a byte mod 40), kernel not yet called
     r_k_inv i    +0xdb4  kernel(&cursor) at 0x83584 has returned

   Through the arm s6 holds the name the selector picked (Sel.v `w_name`), not the model: the model is in the spill
   slot LS_M (lf_slots), and s6 is reloaded from it at +0xf2c.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputChk.
Import ListNotations.
Open Scope Z_scope.

Definition LR_j : Z := AF_LLVMFuzzerTestOneInput + 0xd14.      (* 0x834e8 the selector's join        *)
Definition LR_kcall : Z := AF_LLVMFuzzerTestOneInput + 0xdac.  (* 0x83580 a0 := &cursor; jal kernel  *)
Definition LR_kret : Z := AF_LLVMFuzzerTestOneInput + 0xdb4.   (* 0x83588 kernel has returned         *)
Definition LR_b : Z := AF_LLVMFuzzerTestOneInput + 0xe1c.      (* 0x835f0 model_begin is done        *)
Definition LR_t : Z := AF_LLVMFuzzerTestOneInput + 0xe34.      (* 0x83608 both text_bufs returned    *)
Definition LR_z : Z := AF_LLVMFuzzerTestOneInput + 0xe90.      (* 0x83664 wk, wa zeroed, opened read *)
Definition LR_m : Z := AF_LLVMFuzzerTestOneInput + 0xebc.      (* 0x83690 model_read has returned    *)
Definition LR_q : Z := AF_LLVMFuzzerTestOneInput + 0xee0.      (* 0x836b4 check_socket has returned  *)
Definition LR_f : Z := AF_LLVMFuzzerTestOneInput + 0xf0c.      (* 0x836e0 the refused check's block  *)
Definition LR_c : Z := AF_LLVMFuzzerTestOneInput + 0xf1c.      (* 0x836f0 after the name checks      *)
Definition LR_a : Z := AF_LLVMFuzzerTestOneInput + 0xed8.      (* 0x836ac alias_read has returned    *)

(* the frame's shadow with wk (shadow bytes 92 .. 96) in scope, then wa (102 .. 106) too *)
Definition SH_W : list Z := firstn 92 LF_SH0 ++ repeat 0 5 ++ skipn 97 LF_SH0.
Definition SH_R : list Z := firstn 92 LF_SH0 ++ repeat 0 5 ++ firstn 5 (skipn 97 LF_SH0) ++ repeat 0 5 ++ skipn 107 LF_SH0.
Lemma SH_W_len : length SH_W = 112%nat. Proof. reflexivity. Qed.
Lemma SH_R_len : length SH_R = 112%nat. Proof. reflexivity. Qed.
Lemma SH_W_all : forallb (fun i => Z.eqb (nth i SH_W 0)
    (if ((92 <=? i) && (i <? 97))%nat then 0 else nth i LF_SH0 0)) (seq 0 112) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SH_R_all : forallb (fun i => Z.eqb (nth i SH_R 0)
    (if ((102 <=? i) && (i <? 107))%nat then 0 else nth i SH_W 0)) (seq 0 112) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SH_W_nth : forall i, (i < 112)%nat ->
  nth i SH_W 0 = if ((92 <=? i) && (i <? 97))%nat then 0 else nth i LF_SH0 0.
Proof.
  intros i Hi. pose proof SH_W_all as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. exact H.
Qed.
Lemma SH_R_nth : forall i, (i < 112)%nat ->
  nth i SH_R 0 = if ((102 <=? i) && (i <? 107))%nat then 0 else nth i SH_W 0.
Proof.
  intros i Hi. pose proof SH_R_all as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. exact H.
Qed.

(* the read's strings for a zero cap, and their length *)
Lemma r_kind_nil : forall tab nm kc ac reqs K, kc < 1 -> r_kind (read_core tab nm kc ac reqs K) = [].
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core. destruct nm as [s|]; [|reflexivity].
  destruct (Nat.eqb (length s) 0); [reflexivity|]. destruct (index_of tab s =? 0); [reflexivity|]. cbn [r_kind].
  replace (kc <? 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma r_alias_nil : forall tab nm kc ac reqs K, ac < 1 -> r_alias (read_core tab nm kc ac reqs K) = [].
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core. destruct nm as [s|]; [|reflexivity].
  destruct (Nat.eqb (length s) 0); [reflexivity|]. destruct (index_of tab s =? 0); [reflexivity|]. cbn [r_alias].
  replace (ac <? 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* zero bytes hold the empty string *)
Lemma r_acstr_nil_of_zeros : forall segs m a n, abytes segs m a (repeat (Z_to_bv 8 0) n) -> (1 <= n)%nat ->
  acstr_at segs m a [].
Proof.
  intros segs m a n (H0 & H1 & H2) Hn. split; [|intros []].
  split; [exact H0|]. cbn [app length]. rewrite repeat_length in H1. split; [lia|].
  intros i Hi. destruct i as [|i]; [|lia]. rewrite (H2 0%nat ltac:(rewrite repeat_length; lia)).
  destruct n as [|n]; [lia|]. reflexivity.
Qed.

(* a text buffer's guard byte *)
Lemma r_au8arr_guard : forall segs m t c bs, atbuf_at segs m t c bs -> au8arr segs m (t + c) [zb GUARD_BYTE].
Proof.
  intros segs m t c bs (((H0 & H1 & H2) & Hw) & Hl). rewrite length_app in H1. cbn [length] in H1.
  unfold awrange in Hw. rewrite length_app in Hw. cbn [length] in Hw.
  split.
  - split; [lia|]. cbn [length]. split; [lia|].
    intros i Hi. destruct i as [|i]; [|cbn in Hi; lia]. rewrite Z.add_0_r.
    pose proof (H2 (length bs) ltac:(rewrite length_app; cbn [length]; lia)) as Hg.
    rewrite nth_error_app2 in Hg by lia. rewrite Nat.sub_diag in Hg. rewrite <- Hl. exact Hg.
  - intros i Hi. cbn [length] in Hi. replace (t + c + i) with (t + Z.of_nat (length bs) + i) by lia.
    rewrite <- Z.add_assoc. apply Hw. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variables LF_MO_SET LF_MO_OP : Z.

(* the loop registers of lf_lregs with the name in s6, and the two sizes in s2 / s4 *)
Definition r_regs (cx : lcx) (md fp i s kc ac : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 18 = w64 kc /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 20 = w64 ac /\
  getr (ms_regs ms3) 21 = w64 (md + MD_N_MARK) /\
  getr (ms_regs ms3) 22 = w64 s /\
  getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

(* what every cut of the arm carries *)
Definition r_mem (i md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (sh : list Z)
    (cx : lcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
    : Prop :=
  0 <= i <= 47 /\ lf_core cx ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 sh /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3
    T3 [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * i.

(* +0xdac: the name and the two sizes are read, the call of kernel is next *)
Definition r_d_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte)) (kc ac : Z),
  lf_shape fy LR_kcall ms3 /\ r_regs cx md fp i s kc ac ms3 /\ w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\
  r_mem i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3.

(* +0xdb4: kernel has returned *)
Definition r_k_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte)) (kc ac : Z),
  lf_shape fy LR_kret ms3 /\ r_regs cx md fp i s kc ac ms3 /\ w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\
  r_mem i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 /\ nk_next kbs = 0.

(* from +0xe04 on: s5 := kc, s11 := ac (the loop's s5 and shadow base are reloaded at +0xf4c / +0xf50) *)
Definition r_regs2 (cx : lcx) (fp i s kc ac : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 18 = w64 kc /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 20 = w64 ac /\
  getr (ms_regs ms3) 21 = w64 kc /\
  getr (ms_regs ms3) 22 = w64 s /\
  getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 ac.

(* +0xe1c: model_begin's five stores are done, the first text_buf is next. The model and g_nl start the read
   with no request owed and the model's kernel state the kernel's (the two sides of link_spec's read_agree) *)
Definition r_b_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte)) (kc ac : Z),
  lf_shape fy LR_b ms3 /\ r_regs2 cx fp i s kc ac ms3 /\ w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\
  r_mem i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 /\
  nk_n_sent kbs = 0 /\ md_reqs mbs = [] /\ md_kstate mbs kbs = nk_kstate kbs /\ requests_are kbs mbs.

(* a text_buf(cap)'s answer t and the block it adds: none for cap = 0 (NULL), else the fresh (t, cap + 1) *)
Definition tb_nb (cap t : Z) (nb : list (Z * Z)) : Prop :=
  (cap = 0 /\ t = 0 /\ nb = []) \/ (1 <= cap /\ 4096 <= t /\ nb = [(t, cap + 1)]).

(* from +0xe30 on: s7 := kind = text_buf(kc), s10 := alias = text_buf(ac) *)
Definition r_regs3 (cx : lcx) (fp i s kc ac t1 t2 : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 18 = w64 kc /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 20 = w64 ac /\
  getr (ms_regs ms3) 21 = w64 kc /\
  getr (ms_regs ms3) 22 = w64 s /\
  getr (ms_regs ms3) 23 = w64 t1 /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 t2 /\
  getr (ms_regs ms3) 27 = w64 ac.

(* the two fresh buffers: blocks of the state, new since the call, apart from the cut's blocks; all 0x5a *)
Definition r_bufs (cx : lcx) (md mk : Z) (T3 : list (Z * Z)) (ly3 : alayout) (S3 : astate) (m : word -> option byte)
    (kc ac t1 t2 : Z) (nb1 nb2 : list (Z * Z)) : Prop :=
  tb_nb kc t1 nb1 /\ tb_nb ac t2 nb2 /\
  (forall b, In b (nb1 ++ nb2) -> In b (ablocks B ly3 S3) /\ ~ In b (ablocks B (c_ly cx) (c_S cx)) /\
     (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
        zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)))) /\
  (forall b1 b2, In b1 nb1 -> In b2 nb2 -> zdisjoint (fst b1, req_size (snd b1)) (fst b2, req_size (snd b2))).

(* +0xe34: both text_bufs have returned *)
Definition r_t_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte)) (kc ac : Z)
    (t1 t2 : Z) (nb1 nb2 : list (Z * Z)),
  lf_shape fy LR_t ms3 /\ r_regs3 cx fp i s kc ac t1 t2 ms3 /\ w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\
  0 <= i <= 47 /\ lf_core cx ms3 /\
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb2 ++ nb1 ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 2) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) k2 ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\
  nk_n_sent kbs = 0 /\ md_reqs mbs = [] /\ md_kstate mbs kbs = nk_kstate kbs /\ requests_are kbs mbs /\
  r_bufs cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) kc ac t1 t2 nb1 nb2 /\
  (1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem ms3)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))) /\
  (1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem ms3)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))).
(* from +0xe4c on: s2 := wk = F + 0x2e0, s4 := wa = F + 0x330 *)
Definition r_regs4 (cx : lcx) (fp i s kc ac t1 t2 : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 18 = w64 (lf_F cx fp + LO_B2E0) /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 20 = w64 (lf_F cx fp + LO_B330) /\
  getr (ms_regs ms3) 21 = w64 kc /\
  getr (ms_regs ms3) 22 = w64 s /\
  getr (ms_regs ms3) 23 = w64 t1 /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 t2 /\
  getr (ms_regs ms3) 27 = w64 ac.

(* +0xe90: the two size bytes' wk / wa (F + 0x2e0, F + 0x330, 40 bytes each) are zero and in scope, and the count
   of sockets opened so far is in the slot at s1 + 0x70 *)
Definition r_z_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte)) (kc ac : Z)
    (t1 t2 : Z) (nb1 nb2 : list (Z * Z)),
  lf_shape fy LR_z ms3 /\
  r_regs4 cx fp i s kc ac t1 t2 ms3 /\ w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\
  0 <= i <= 47 /\ lf_core cx ms3 /\
  chk_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb2 ++ nb1 ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 2) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) k2 SH_R ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\
  nk_n_sent kbs = 0 /\ md_reqs mbs = [] /\ md_kstate mbs kbs = nk_kstate kbs /\ requests_are kbs mbs /\
  r_bufs cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) kc ac t1 t2 nb1 nb2 /\
  (1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem ms3)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))) /\
  (1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem ms3)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))) /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B2E0) (repeat (Z_to_bv 8 0) 40) /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B330) (repeat (Z_to_bv 8 0) 40) /\
  lf_slot cx W3 ms3 LS_NIF (nk_opened kbs).

(* the model's answer to the read: read_model on g_nl's table, with no request owed and the kernel's chunk state *)
Definition r_RR (nm : option (list byte)) (kc ac : Z) (kbs : list byte) : rres :=
  read_model lf_tab nm kc ac [] (nk_kstate kbs).

(* +0xebc: model_read has returned; want in a0, the model holds its answer, wk and wa its two strings *)
Definition r_m_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte)) (kc ac : Z)
    (t1 t2 : Z) (nb1 nb2 : list (Z * Z)),
  lf_shape fy LR_m ms3 /\
  r_regs4 cx fp i s kc ac t1 t2 ms3 /\ getr (ms_regs ms3) 10 = w64 (r_rc (r_RR nm kc ac kbs)) /\
  w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= i <= 47 /\ lf_core cx ms3 /\
  chk_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb2 ++ nb1 ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 2) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) k2 SH_R ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\ nk_n_sent kbs = 0 /\
  md_reqs mbs = r_reqs (r_RR nm kc ac kbs) /\ md_kstate mbs kbs = r_state (r_RR nm kc ac kbs) /\
  r_bufs cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) kc ac t1 t2 nb1 nb2 /\
  (1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem ms3)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))) /\
  (1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem ms3)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))) /\
  (acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B2E0) (r_kind (r_RR nm kc ac kbs)) /\
     (1 <= kc -> abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B2E0) kc)) /\
  (acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B330) (r_alias (r_RR nm kc ac kbs)) /\
     (1 <= ac -> abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B330) ac)) /\
  lf_slot cx W3 ms3 LS_NIF (nk_opened kbs).

(* the library's answer: read_lib on the same table, the requests g_nl has sent (none) and its chunk state *)
Definition r_LR (nm : option (list byte)) (kc ac : Z) (kbs : list byte) : rres :=
  read_lib lf_tab nm kc ac [] (nk_kstate kbs).

(* from +0xebc on: s4 := want *)
Definition r_regs5 (cx : lcx) (fp i s kc ac t1 t2 want : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 18 = w64 (lf_F cx fp + LO_B2E0) /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 20 = w64 want /\
  getr (ms_regs ms3) 21 = w64 kc /\
  getr (ms_regs ms3) 22 = w64 s /\
  getr (ms_regs ms3) 23 = w64 t1 /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 t2 /\
  getr (ms_regs ms3) 27 = w64 ac.

(* +0xed8: reac_link_alias_read has returned; rc in a0, g_nl the library's new bytes kbs', the model's answer kept *)
Definition r_a_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs kbs' mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte))
    (kc ac t1 t2 : Z) (nb1 nb2 : list (Z * Z)),
  lf_shape fy LR_a ms3 /\
  r_regs5 cx fp i s kc ac t1 t2 (r_rc (r_RR nm kc ac kbs)) ms3 /\
  getr (ms_regs ms3) 10 = w64 (r_rc (r_LR nm kc ac kbs)) /\
  w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= i <= 47 /\ lf_core cx ms3 /\
  chk_cut SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 (nb2 ++ nb1 ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 2) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) k2 SH_R ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\
  nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1 /\
  ((nm = None \/ nm = Some [] \/ (forall x, nm = Some x -> index_of lf_tab x = 0)) -> nk_opened kbs' = nk_opened kbs) /\
  nk_sent kbs' = r_reqs (r_LR nm kc ac kbs) /\ nk_n_sent kbs' = Z.of_nat (length (r_reqs (r_LR nm kc ac kbs))) /\
  nk_kstate kbs' = r_state (r_LR nm kc ac kbs) /\
  md_reqs mbs = r_reqs (r_RR nm kc ac kbs) /\ md_kstate mbs kbs' = r_state (r_RR nm kc ac kbs) /\
  r_bufs cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) kc ac t1 t2 nb1 nb2 /\
  (1 <= kc -> acstr_at SEGS (rdW W3 (ms_mem ms3)) t1 (r_kind (r_LR nm kc ac kbs)) /\
     abuf SEGS (rdW W3 (ms_mem ms3)) t1 kc /\ au8arr SEGS (rdW W3 (ms_mem ms3)) (t1 + kc) [zb GUARD_BYTE]) /\
  (1 <= ac -> acstr_at SEGS (rdW W3 (ms_mem ms3)) t2 (r_alias (r_LR nm kc ac kbs)) /\
     abuf SEGS (rdW W3 (ms_mem ms3)) t2 ac /\ au8arr SEGS (rdW W3 (ms_mem ms3)) (t2 + ac) [zb GUARD_BYTE]) /\
  (acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B2E0) (r_kind (r_RR nm kc ac kbs)) /\
     (1 <= kc -> abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B2E0) kc)) /\
  (acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B330) (r_alias (r_RR nm kc ac kbs)) /\
     (1 <= ac -> abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B330) ac)) /\
  lf_slot cx W3 ms3 LS_NIF (nk_opened kbs) /\
  - 2 ^ 32 < r_rc (r_LR nm kc ac kbs) < 2 ^ 32.

(* from +0xed8 on: s2 := rc *)
Definition r_regs6 (cx : lcx) (fp i s kc ac t1 t2 want rc : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 18 = w64 rc /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 20 = w64 want /\
  getr (ms_regs ms3) 21 = w64 kc /\
  getr (ms_regs ms3) 22 = w64 s /\
  getr (ms_regs ms3) 23 = w64 t1 /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 t2 /\
  getr (ms_regs ms3) 27 = w64 ac.

(* the refused cases (fuzz_link.c op_read: !name || !name[0] || !index_of(name)) *)
Definition r_refused (nm : option (list byte)) : Prop :=
  nm = None \/ nm = Some [] \/ (forall x, nm = Some x -> index_of lf_tab x = 0).

(* the facts of the arm's buffers a stretch of calls that write none of them keeps: the two text buffers, wk and wa,
   and the slot that holds g_nl.opened before alias_read; and the range of the library's code *)
Definition r_ext (cx : lcx) (fp md mk : Z) (T3 : list (Z * Z)) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (kbs : list byte) (nm : option (list byte)) (kc ac t1 t2 : Z) (nb1 nb2 : list (Z * Z))
    : Prop :=
  r_bufs cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) kc ac t1 t2 nb1 nb2 /\
  (1 <= kc -> acstr_at SEGS (rdW W3 (ms_mem ms3)) t1 (r_kind (r_LR nm kc ac kbs)) /\
     abuf SEGS (rdW W3 (ms_mem ms3)) t1 kc /\ au8arr SEGS (rdW W3 (ms_mem ms3)) (t1 + kc) [zb GUARD_BYTE]) /\
  (1 <= ac -> acstr_at SEGS (rdW W3 (ms_mem ms3)) t2 (r_alias (r_LR nm kc ac kbs)) /\
     abuf SEGS (rdW W3 (ms_mem ms3)) t2 ac /\ au8arr SEGS (rdW W3 (ms_mem ms3)) (t2 + ac) [zb GUARD_BYTE]) /\
  (acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B2E0) (r_kind (r_RR nm kc ac kbs)) /\
     (1 <= kc -> abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B2E0) kc)) /\
  (acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B330) (r_alias (r_RR nm kc ac kbs)) /\
     (1 <= ac -> abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B330) ac)) /\
  lf_slot cx W3 ms3 LS_NIF (nk_opened kbs) /\
  - 2 ^ 32 < r_rc (r_LR nm kc ac kbs) < 2 ^ 32.

(* the checks' stretch, +0xed8 .. +0xf1c: what every state of it carries (registers and memory), and a fact Q of the
   state and the name; r_c adds the pc *)
Definition r_cm (Q : machine_state -> option (list byte) -> Prop) (i : Z) (cx : lcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs kbs' mbs gbs : list byte) (T3 : list (Z * Z)) (s : Z) (nm : option (list byte))
    (kc ac t1 t2 : Z) (nb1 nb2 : list (Z * Z)),
  r_regs6 cx fp i s kc ac t1 t2 (r_rc (r_RR nm kc ac kbs)) (r_rc (r_LR nm kc ac kbs)) ms3 /\
  w_name s nm /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= i <= 47 /\ lf_core cx ms3 /\
  chk_cut SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 (nb2 ++ nb1 ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 2) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) k2 SH_R ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\
  nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1 /\
  (r_refused nm -> nk_opened kbs' = nk_opened kbs) /\
  nk_sent kbs' = r_reqs (r_LR nm kc ac kbs) /\ nk_n_sent kbs' = Z.of_nat (length (r_reqs (r_LR nm kc ac kbs))) /\
  nk_kstate kbs' = r_state (r_LR nm kc ac kbs) /\
  md_reqs mbs = r_reqs (r_RR nm kc ac kbs) /\ md_kstate mbs kbs' = r_state (r_RR nm kc ac kbs) /\
  r_ext cx fp md mk T3 ly3 S3 W3 ms3 kbs nm kc ac t1 t2 nb1 nb2 /\
  Q ms3 nm.

Definition r_c (pc : Z) (Q : machine_state -> option (list byte) -> Prop) (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z)
    (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  lf_shape fy pc ms3 /\ r_cm Q i cx fp k2 ly3 S3 W3 ms3 md3.


End b.
End a.
