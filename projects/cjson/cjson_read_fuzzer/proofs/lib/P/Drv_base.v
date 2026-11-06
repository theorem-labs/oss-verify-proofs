(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RSN : nat := 65536.
Arguments RSN : simpl never.
Lemma RSN_Z : Z.of_nat RSN = 65536.
Proof. reflexivity. Qed.
#[global] Opaque RSN.   (* [comment removed for export] *)

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PMAIN    : Z := 0x1214c.
Definition PTRUN    : Z := 0x1241c.   (* [comment removed for export] *)
Definition PEMIT    : Z := 0x125a4.   (* [comment removed for export] *)
Definition PFUZZE   : Z := 0x125ec.   (* [comment removed for export] *)
Definition PEXITF   : Z := 0x14fb4.   (* [comment removed for export] *)
Definition PFPRINTF : Z := 0x174f0.
Definition PFWRITE  : Z := 0x1768c.
Definition POPEN    : Z := 0x15044.
Definition PREAD    : Z := 0x213b4.
Definition PCLOSE   : Z := 0x21354.
Definition PMEMCPY  : Z := 0x209e8.
Definition PSTAGE2_RET : Z := 0x14b1c.   (* [comment removed for export] *)
Definition PINITFLAG : Z := 0x33780.     (* [comment removed for export] *)
Definition PINCB    : Z := 0x33784.      (* [comment removed for export] *)
Definition PATEX    : Z := 0x538d0.      (* [comment removed for export] *)
Definition PATEXITF : Z := 0x14e9c.      (* [comment removed for export] *)
Definition PDSO     : Z := 0x23500.      (* [comment removed for export] *)
Definition PCXAFIN  : Z := 0x14e98.      (* [comment removed for export] *)
Definition PRS : Z := 0x23779.           (* [comment removed for export] *)
Lemma PRS_eq : PRS = 0x23779.   (* [comment removed for export] *)
Proof. reflexivity. Qed.


(* [comment removed for export] *)
Definition mframe (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word) : list cell :=
  [CB 8 fj; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra0].

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_step_evt : forall ms mo T,
  MOK mo -> evt psegs (fun ms' => realizes psegs (mkCfg ms' mo) T) ms -> realizes psegs (mkCfg ms mo) T.
Proof. intros ms mo T HM He. eapply rz_evt; [exact HM| exact He|]. intros ms' H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition DSTAT (ph : bool) (tid : word) (m : word -> option byte) : Prop :=
  rw_cells psegs m 0x337c8 [C8 (wz 0x337c8); C8 (wz 0x337c8); C8 (wz 0x337c8); C8 (wz 0); C4 tid]   (* [comment removed for export] *)
  /\ rw_cells psegs m 0x53af0 [C4 (wz 0)]                                                          (* [comment removed for export] *)
  /\ rw_cells psegs m 0x224f0 [C8 (wz 0x223f8); C8 (wz 0x223f0)]                                    (* [comment removed for export] *)
  /\ rw_cells psegs m 0x223f0 [C8 (wz 0x120bc)]                                                    (* [comment removed for export] *)
  /\ rw_cells psegs m 0x23778 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ rw_cells psegs m 0x22498 [C8 (wz PCXAFIN); C8 (wz 0)]                                        (* [comment removed for export] *)
  /\ rw_cells psegs m 0x53f48 [C8 (wz 0)]                                                          (* [comment removed for export] *)
  /\ rw_cells psegs m 0x53f38 [C8 (wz 0)]                                                          (* [comment removed for export] *)
  /\ rw_cells psegs m 0x23718 [C8 (wz RSTDOUT)]                                                    (* [comment removed for export] *)
  /\ rw_cells psegs m 0x23628 [C8 (wz RSTDERR)]                                                    (* [comment removed for export] *)
  /\ rw_cells psegs m 0x224a8 [C8 (wz 0x22458)]                                                    (* [comment removed for export] *)
  /\ rw_cells psegs m 0x22458 [C8 (wz RSTDERR)]                                                    (* [comment removed for export] *)
  /\ rw_cells psegs m 0x224b0 [C8 (wz 0)]                                                          (* [comment removed for export] *)
  /\ rw_cells psegs m PDSO [C8 (wz PDSO)]                                                         (* [comment removed for export] *)
  /\ rw_cells psegs m PINCB [C1 (Z_to_bv 8 0)]                                                    (* [comment removed for export] *)
  /\ ATEX ph m.                                                                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dstat_addr (a : Z) : Prop :=
  (0x337c8 <= a < 0x337ec) \/ (0x53af0 <= a < 0x53af4) \/ (0x224f0 <= a < 0x22500) \/ (0x223f0 <= a < 0x223f8)
  \/ (0x23778 <= a < 0x23779) \/ (0x22498 <= a < 0x224a8) \/ (0x53f48 <= a < 0x53f50) \/ (0x53f38 <= a < 0x53f40)
  \/ (0x23718 <= a < 0x23720) \/ (0x23628 <= a < 0x23630) \/ (0x224a8 <= a < 0x224c0) \/ (0x22458 <= a < 0x22468)
  \/ (0x23500 <= a < 0x23508) \/ (0x33784 <= a < 0x33785) \/ (0x538d0 <= a < 0x538f8) \/ (0x539f0 <= a < 0x539f8).

Lemma DSTAT_magree : forall ph tid m m', DSTAT ph tid m -> magree dstat_addr m m' -> DSTAT ph tid m'.
Proof.
  intros ph tid m m' D AG. unfold DSTAT, ATEX, PDSO, PINCB, PATEX in *.
  destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17).
  repeat match goal with |- _ /\ _ => split end.
  all: eapply rw_cells_magree; [exact AG| eassumption| cbn [cells_size atex_cells csize Nat.add]; unfold dstat_addr; intros; lia].
Qed.

(* [comment removed for export] *)
Lemma dstat_doc_addr : forall LB SP a, dstat_addr a -> doc_addr LB SP a.
Proof.
  intros LB SP a Ha. unfold doc_addr, cj_client_addr, palloc_static, dstat_addr, PDSO, PINCB, PATEX, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP, PGERROR in *.
  split; [right; left; lia| lia].
Qed.

Lemma DSTAT_dpres : forall ph tid LB SP m m', DSTAT ph tid m -> dpres LB SP m m' -> DSTAT ph tid m'.
Proof.
  intros ph tid LB SP m m' D PR. eapply DSTAT_magree; [exact D|]. eapply magree_mono; [exact PR|]. intros a Ha. apply dstat_doc_addr. exact Ha.
Qed.

Lemma DSTAT_cj_pres : forall ph tid LB SP m m', DSTAT ph tid m -> cj_pres LB SP m m' -> DSTAT ph tid m'.
Proof.
  intros ph tid LB SP m m' D PR. eapply DSTAT_magree; [exact D|]. intros a Ha Hd. apply PR; [exact Ha|]. exact (proj1 (dstat_doc_addr LB SP a Hd)).
Qed.

(* [comment removed for export] *)
Definition dstat_safe (iv : Z * Z) : Prop :=
  snd iv <= fst iv \/ 0x55000 <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDERR + 232) \/ (RSTDOUT <= fst iv /\ snd iv <= RSTDOUT + 232)
  \/ (RSTDOUT_BUF <= fst iv /\ snd iv <= RSTDOUT_BUF + 1024) \/ (PERRNO <= fst iv /\ snd iv <= PERRNO + 4) \/ snd iv <= 0x10000
  \/ (PRS <= fst iv /\ snd iv <= PRS + 65536).

Lemma outside_of_Forall : forall (P : Z * Z -> Prop) W x,
  Forall P W -> (forall lo hi, P (lo, hi) -> ~ (lo <= x < hi)) -> outside W x.
Proof.
  intros P W x FW HP. induction FW as [|[lo hi] W Hx FW IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

Lemma DSTAT_munch : forall ph tid W m m', DSTAT ph tid m -> munch W m m' -> wmono psegs m m' -> Forall dstat_safe W -> DSTAT ph tid m'.
Proof.
  intros ph tid W m m' D MU WM FW. eapply DSTAT_magree; [exact D|].
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha Hd.
  eapply outside_of_Forall; [exact FW|]. intros lo hi Hx. unfold dstat_safe, dstat_addr, PERRNO, PRS in *. cbn [fst snd] in Hx. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FDS0 : list (word * FdEntry) :=
  [(wz 0, FdChannel (wz 0)); (wz 1, FdChannel (wz 1)); (wz 2, FdChannel (wz 2))].
Definition FDS3 (e : FdEntry) : list (word * FdEntry) :=
  [(wz 3, e); (wz 0, FdChannel (wz 0)); (wz 1, FdChannel (wz 1)); (wz 2, FdChannel (wz 2))].

Lemma FDS0_alloc : alloc_fd FDS0 = wz 3. Proof. reflexivity. Qed.
Lemma FDS0_3 : fd_lookup FDS0 (wz 3) = None. Proof. reflexivity. Qed.
Lemma FDS0_insert : forall e, fd_insert FDS0 (alloc_fd FDS0) e = FDS3 e. Proof. reflexivity. Qed.
Lemma FDS3_insert : forall e e', fd_insert (FDS3 e) (wz 3) e' = FDS3 e'. Proof. reflexivity. Qed.
Lemma FDS3_remove : forall e, fd_remove (FDS3 e) (wz 3) = FDS0. Proof. reflexivity. Qed.
Lemma FDS3_3 : forall e, fd_lookup (FDS3 e) (wz 3) = Some e. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record DMOD (fs : Fs) (F : list (word * FdEntry)) (mo : Model) : Prop := mkDMOD {
  dm_mok : MOK mo; dm_fds : m_fds mo = F; dm_fs : m_fs mo = fs }.

Lemma DMOD_chan : forall fs F mo, DMOD fs F mo -> (F = FDS0 \/ exists e, F = FDS3 e) -> chan_ok mo 1 /\ chan_ok mo 2.
Proof.
  intros fs F mo [_ HF _] H. unfold chan_ok. rewrite HF. destruct H as [-> | [e ->]]; split; reflexivity.
Qed.

Lemma DMOD_vm_only : forall fs F mo mo', DMOD fs F mo -> vm_only mo mo' -> MOK mo' -> DMOD fs F mo'.
Proof.
  intros fs F mo mo' [HM HF HS] VO HM'. destruct (vm_only_facts mo mo' VO) as (E1 & E2 & _).
  split; [exact HM'| |]; rewrite ?E1, ?E2; auto.
Qed.

Lemma DMOD_with_fds : forall fs F F' mo, DMOD fs F mo -> DMOD fs F' (with_fds F' mo).
Proof.
  intros fs F F' mo [[HM1 HM2] HF HS]. split; [split| |]; autorewrite with model; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition file_safe (iv : Z * Z) : Prop :=
  snd iv <= fst iv \/ 0x55000 <= fst iv \/ snd iv <= RSTDERR \/ (RSTDOUT + 232 <= fst iv /\ snd iv <= RSTDOUT_BUF) \/ RSTDOUT_BUF + 1024 <= fst iv /\ snd iv <= 0x55000 \/ snd iv <= 0x10000.

Lemma disjoint_from_Forall : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof. intros P W a n FW HP. induction FW as [|[lo hi] W Hx FW IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH]. Qed.

Lemma stdout_file_munch : forall m m' so W,
  stdout_file m so -> munch W m m' -> wmono psegs m m' ->
  Forall (fun iv => (snd iv <= RSTDOUT \/ RSTDOUT + 232 <= fst iv) /\ (snd iv <= RSTDOUT_BUF \/ RSTDOUT_BUF + 1024 <= fst iv)) W ->
  stdout_file m' so.
Proof.
  intros m m' so W (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM FW.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn [cells_size file_cells csize Nat.add]. cbn [fst snd]; intros lo hi [H _]; lia.
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn [cells_size csize Nat.add]. cbn [fst snd]; intros lo hi [_ H]; lia.
Qed.

Lemma stderr_wfile0_munch : forall m m' W,
  stderr_wfile0 m -> munch W m m' -> wmono psegs m m' ->
  Forall (fun iv => snd iv <= RSTDERR \/ RSTDERR + 232 <= fst iv) W -> stderr_wfile0 m'.
Proof.
  intros m m' W (flags & mode & e & wend & tail & FC & H) MU WM FW.
  exists flags, mode, e, wend, tail. split; [| exact H].
  eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn [cells_size file_cells csize Nat.add]. cbn [fst snd]; intros lo hi HH; lia.
Qed.

Lemma stderr_wfile_munch : forall m m' W,
  stderr_wfile m -> munch W m m' -> wmono psegs m m' ->
  Forall (fun iv => snd iv <= RSTDERR \/ RSTDERR + 232 <= fst iv) W -> stderr_wfile m'.
Proof.
  intros m m' W (flags & mode & e & wend & tail & FC & H) MU WM FW.
  exists flags, mode, e, wend, tail. split; [| exact H].
  eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn [cells_size file_cells csize Nat.add]. cbn [fst snd]; intros lo hi HH; lia.
Qed.

(* [comment removed for export] *)
Lemma stdout_file_magree : forall m m' so (P : Z -> Prop),
  stdout_file m so -> magree P m m' -> (forall a, (RSTDOUT <= a < RSTDOUT + 232) \/ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024) -> P a) -> stdout_file m' so.
Proof.
  intros m m' so P (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) AG HP.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_magree; [exact AG| exact FC| cbn [cells_size file_cells csize Nat.add]; intros; apply HP; lia].
  - eapply rw_cells_magree; [exact AG| exact BUF| cbn [cells_size csize Nat.add]; intros; apply HP; lia].
Qed.

Lemma stderr_wfile0_magree : forall m m' (P : Z -> Prop),
  stderr_wfile0 m -> magree P m m' -> (forall a, RSTDERR <= a < RSTDERR + 232 -> P a) -> stderr_wfile0 m'.
Proof.
  intros m m' P (flags & mode & e & wend & tail & FC & H) AG HP.
  exists flags, mode, e, wend, tail. split; [| exact H].
  eapply rw_cells_magree; [exact AG| exact FC| cbn [cells_size file_cells csize Nat.add]; intros; apply HP; lia].
Qed.

Lemma file_doc_addr : forall LB SP a,
  (RSTDOUT <= a < RSTDOUT + 232) \/ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024) \/ (RSTDERR <= a < RSTDERR + 232) -> doc_addr LB SP a.
Proof.
  intros LB SP a Ha. unfold doc_addr, cj_client_addr, palloc_static, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP, PGERROR in *.
  split; [right; left; lia| lia].
Qed.

Lemma stdout_file_cj_pres : forall LB SP m m' so, stdout_file m so -> cj_pres LB SP m m' -> stdout_file m' so.
Proof.
  intros LB SP m m' so H PR. eapply (stdout_file_magree m m' so (cj_client_addr LB SP)); [exact H| apply (proj1 (cj_pres_magree _ _ _ _)); exact PR|].
  intros a Ha. exact (proj1 (file_doc_addr LB SP a ltac:(destruct Ha; auto))).
Qed.
Lemma stdout_file_dpres : forall LB SP m m' so, stdout_file m so -> dpres LB SP m m' -> stdout_file m' so.
Proof.
  intros LB SP m m' so H PR. eapply stdout_file_magree; [exact H| exact PR|]. intros a Ha. apply file_doc_addr. destruct Ha; auto.
Qed.
Lemma stderr_wfile0_cj_pres : forall LB SP m m', stderr_wfile0 m -> cj_pres LB SP m m' -> stderr_wfile0 m'.
Proof.
  intros LB SP m m' H PR. eapply (stderr_wfile0_magree m m' (cj_client_addr LB SP)); [exact H| apply (proj1 (cj_pres_magree _ _ _ _)); exact PR|].
  intros a Ha. exact (proj1 (file_doc_addr LB SP a ltac:(auto))).
Qed.
Lemma stderr_wfile0_dpres : forall LB SP m m', stderr_wfile0 m -> dpres LB SP m m' -> stderr_wfile0 m'.
Proof.
  intros LB SP m m' H PR. eapply stderr_wfile0_magree; [exact H| exact PR|]. intros a Ha. apply file_doc_addr. auto.
Qed.

(* [comment removed for export] *)
Lemma t_eq_emit : forall o K K', t_eq K K' -> t_eq (t_emit o K) (t_emit o K').
Proof.
  intros o K K' H tr. unfold t_emit. split; intros [Hp | (tr' & -> & HK)]; try (left; exact Hp); right; exists tr'; split; auto; apply H; exact HK.
Qed.

Lemma t_exit_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit, t_emit. left. apply is_prefix_nil. Qed.

Lemma t_emit_has_nil' : forall o K, t_emit o K [].
Proof. intros. unfold t_emit. left. apply is_prefix_nil. Qed.

(* [comment removed for export] *)
Lemma rz_drop_nil : forall c K, K [] -> realizes psegs c (t_emit (W 1 []) K) -> realizes psegs c K.
Proof. intros c K HK H. eapply rz_conseq; [exact H|]. cbn [W map]. apply t_emit_nil_eq. exact HK. Qed.

Lemma rz_die : forall c msg fs,
  realizes psegs c (t_emit (W 2 msg) (t_emit (W 1 []) (t_exit (wz 2) fs))) -> realizes psegs c (t_die msg fs).
Proof.
  intros c msg fs H. unfold t_die. eapply rz_conseq; [exact H|]. apply t_eq_emit. cbn [W map]. apply t_emit_nil_eq. apply t_exit_nil.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition spec_path (path : list byte) (fs0 : Fs) : TSet :=
  if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
  else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0
  else if list_byte_eqb path dot_path then t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
  else match fs_lookup fs0 path with
       | None => t_die (msg_cannot_open path) fs0
       | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)
       end.

Lemma spec_two : forall a0 path fs0, spec [a0; path] fs0 = spec_path path fs0.
Proof. reflexivity. Qed.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

Lemma list_byte_eqb_neq : forall p q, list_byte_eqb p q = false <-> p <> q.
Proof.
  intros p q. destruct (list_byte_eqb p q) eqn:E.
  - apply list_byte_eqb_eq in E. split; [discriminate| intros H; exfalso; exact (H E)].
  - split; [| reflexivity]. intros _ H. apply (proj2 (list_byte_eqb_eq p q)) in H. congruence.
Qed.

(* [comment removed for export] *)
Lemma errno_addr_tp : forall tp, tp = wz PTP -> bv_unsigned tp + -164 = PERRNO.
Proof. intros tp ->. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac solve_Forall tac := repeat (apply Forall_cons; [tac|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac xport H MU WM H' :=
  lazymatch type of H with
  | DSTAT _ _ _ => pose proof (DSTAT_munch _ _ _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold dstat_safe, PERRNO, PINITFLAG, PRS; cbn [fst snd]; lia))) as H'
  | stdout_file _ _ => pose proof (stdout_file_munch _ _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold PERRNO, PRS; cbn [fst snd]; lia))) as H'
  | stderr_wfile0 _ => pose proof (stderr_wfile0_munch _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold PERRNO, PRS; cbn [fst snd]; lia))) as H'
  | stderr_wfile _ => pose proof (stderr_wfile_munch _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold PERRNO, PRS; cbn [fst snd]; lia))) as H'
  | rw_cells _ _ _ _ => pose proof (rw_cells_transport _ _ _ _ _ _ H MU WM ltac:(pose proof RSN_Z; cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia)) as H'
  | bytes_at _ _ _ _ => pose proof (bytes_at_transport _ _ _ _ _ _ H MU ltac:(cbn -[Z.add Z.mul Z.of_nat]; rewrite ?length_app; cbn [length]; unfold PERRNO, PRS; lia)) as H'
  | ssp_cells _ ?c => let G1 := fresh in let G2 := fresh in destruct H as [G1 G2];
              lazymatch type of MU with munch _ _ ?m' =>
              assert (H' : ssp_cells m' c); [split;
                [ (eapply rw_cells_transport; [exact G1| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia])
                | (eapply rw_cells_transport; [exact G2| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia]) ]|] end   (* [comment removed for export] *)
  | CJST _ => let C1 := fresh in let C2 := fresh in let C3 := fresh in let e1 := fresh in let e2 := fresh in
              destruct H as (C1 & (e1 & e2 & C2) & C3);
              lazymatch type of MU with munch _ _ ?m' =>
              assert (H' : CJST m'); [split; [| split; [exists e1, e2|]];
                [ (eapply rw_cells_transport; [exact C1| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia])
                | (eapply rw_cells_transport; [exact C2| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia])
                | (eapply rw_cells_transport; [exact C3| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia]) ] |] end   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Lemma t_alt2_idem_l : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. split; intros H; [destruct H as [H|[H|H]]| destruct H as [H|H]]; auto. Qed.

Lemma t_body_nil : forall data fs, t_body data fs [].
Proof.
  intros data fs. unfold t_body, t_die. cbv zeta.
  destruct (MAX_INPUT <=? Z.of_nat (length data)); [apply t_emit_has_nil'|].
  destruct (length data <? 6)%nat; [apply t_emit_has_nil'|].
  destruct (length data <? 6 + Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat; [apply t_emit_has_nil'|].
  apply t_emit_has_nil'.   (* [comment removed for export] *)
Qed.


Lemma rw_cells_bytes_at : forall m A cs, rw_cells psegs m A cs -> bytes_at psegs m A (cells_bytes cs).
Proof. intros m A cs [[_ HB] _]. exact HB. Qed.

Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells psegs m A [CB n bs] -> bytes_at psegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[WF HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. cbn in WF. destruct WF as [WF _]. split; [exact HB| exact WF].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac solve_Forall tac := repeat (apply Forall_cons; [tac|]); apply Forall_nil.
Ltac xport H MU WM H' :=
  lazymatch type of H with
  | DSTAT _ _ _ => pose proof (DSTAT_munch _ _ _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold dstat_safe, PERRNO, PINITFLAG, PRS; cbn [fst snd]; lia))) as H'
  | stdout_file _ _ => pose proof (stdout_file_munch _ _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold PERRNO, PRS; cbn [fst snd]; lia))) as H'
  | stderr_wfile0 _ => pose proof (stderr_wfile0_munch _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold PERRNO, PRS; cbn [fst snd]; lia))) as H'
  | stderr_wfile _ => pose proof (stderr_wfile_munch _ _ _ H MU WM ltac:(solve_Forall ltac:(unfold PERRNO, PRS; cbn [fst snd]; lia))) as H'
  | rw_cells _ _ _ _ => pose proof (rw_cells_transport _ _ _ _ _ _ H MU WM ltac:(pose proof RSN_Z; cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia)) as H'
  | bytes_at _ _ _ _ => pose proof (bytes_at_transport _ _ _ _ _ _ H MU ltac:(cbn -[Z.add Z.mul Z.of_nat]; rewrite ?length_app; cbn [length]; unfold PERRNO, PRS; lia)) as H'
  | ssp_cells _ ?c => let G1 := fresh in let G2 := fresh in destruct H as [G1 G2];
              lazymatch type of MU with munch _ _ ?m' =>
              assert (H' : ssp_cells m' c); [split;
                [ (eapply rw_cells_transport; [exact G1| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia])
                | (eapply rw_cells_transport; [exact G2| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia]) ]|] end   (* [comment removed for export] *)
  | CJST _ => let C1 := fresh in let C2 := fresh in let C3 := fresh in let e1 := fresh in let e2 := fresh in
              destruct H as (C1 & (e1 & e2 & C2) & C3);
              lazymatch type of MU with munch _ _ ?m' =>
              assert (H' : CJST m'); [split; [| split; [exists e1, e2|]];
                [ (eapply rw_cells_transport; [exact C1| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia])
                | (eapply rw_cells_transport; [exact C2| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia])
                | (eapply rw_cells_transport; [exact C3| exact MU| exact WM| cbn; unfold PERRNO, PINITFLAG, PGERROR, PHOOKS, PLCONV, PRS, got_ssp, ssp_guard; lia]) ] |] end   (* [comment removed for export] *)
  end.
